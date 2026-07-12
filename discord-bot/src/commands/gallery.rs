//! `/gallery` — the **universe gallery**, wired to the REAL [`ugc_dregg`] registry.
//!
//! This command used to browse "devnet artworks" through four `DevnetClient` calls that
//! every one of them returned [`DevnetError::Unsupported`](crate::devnet::DevnetError)
//! ("not exposed by the current public node API") — a complete UI over four dead stubs,
//! which rendered as "Gallery Unavailable" every single time. The gallery is now the
//! thing dregg actually has: a gallery of **authored universes** on `ugc-dregg`'s real
//! registry + its **no-cheat verifiable leaderboard**.
//!
//! ## The four verbs
//!
//! | subcommand | what it really does |
//! |------------|---------------------|
//! | `list`     | every published [`Universe`] in the registry (name / author / content address) |
//! | `show`     | one universe + its **leaderboard**: verified completions, ranked by turns-to-win |
//! | `publish`  | mints a REAL procgen universe from a committed seed ([`Universe::daily`]) and publishes it — content-addressed, winnable, re-generable byte-for-byte from its seed |
//! | `play`     | submits a run: the moves are re-executed against a FRESH identically-seeded world; only a completion that **provably reaches the win** is accepted + ranked |
//!
//! ## The no-cheat tooth reaches Discord
//!
//! `play` does not trust the player. [`Registry::submit`] re-drives the submitted moves
//! through the real executor on a fresh world and requires the recorded receipt chain
//! re-verifies to the universe's declared WIN state, with a truthful turn count. A forged
//! or incomplete run is REJECTED — and the embed says *why* ([`RejectReason`] is surfaced
//! verbatim, not swallowed). The old `/gallery bid` signing path is repurposed: the
//! player's cipherclerk now signs their submitted run, binding the completion to their
//! custodial identity (see [`sign_run`]).
//!
//! ## Honest scope
//!
//! * **Persistence gap.** The [`Registry`] is in-memory and per-process (`ugc-dregg`'s
//!   own crate docs name this too). A bot restart drops published universes and their
//!   boards back to [`seed_registry`]'s built-in dungeon. Closing it needs a store the
//!   main loop owns (see the module TODO below) — nothing here is written to `db.rs`.
//! * **Auctions are gone, not stubbed.** `ugc-dregg` has no auction/bid concept, so
//!   `auctions`/`mybids` are NOT carried forward as dead UI. The bidding *machinery*
//!   (cclerk signing) is repurposed onto `play`, which is a real submission.
//! * **Author identity** is a *name*, not a verified signing key (ugc-dregg's own named
//!   gap). The `play` signature binds the *player*; the *author* string is still trusted.
//
// TODO(main-loop, persistence): the registry lives in this module's `OnceLock` because
// `db.rs` and `BotState` are main-loop-owned. To survive a restart it wants either
// (a) a `pub universes: Mutex<ugc_dregg::Registry>` on `BotState`, or (b) a
// `universes(id, name, author, source, deploy_seed, provenance, win)` +
// `completions(universe_id, player, turns, playthrough)` pair of tables, replayed
// through `Registry::publish`/`submit` on boot — which re-verifies every stored
// completion at load, so a tampered DB row cannot resurrect a cheat.

use std::sync::{Mutex, OnceLock};

use serenity::all::{
    CommandDataOptionValue, CommandInteraction, CommandOptionType, Context, CreateCommand,
    CreateCommandOption, CreateInteractionResponse, CreateInteractionResponseMessage,
    EditInteractionResponse,
};

use dungeon_on_dregg::DUNGEON;
use ugc_dregg::{
    Accepted, Completion, Provenance, Registry, RejectReason, Universe, UniverseId, WinCondition,
    record_playthrough,
};

use crate::BotState;
use crate::cipherclerk::{UserCipherclerk, sign_legacy};
use crate::embeds;

// ═══════════════════════════════════════════════════════════════════════════════
// The registry — the real `ugc-dregg` one, in-memory (see the persistence gap above).
// ═══════════════════════════════════════════════════════════════════════════════

/// The process-wide UGC registry. Seeded with the built-in salt-shore dungeon (+ the
/// house's par run) so the gallery is never empty on a cold boot.
fn registry() -> &'static Mutex<Registry> {
    static REGISTRY: OnceLock<Mutex<Registry>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(seed_registry()))
}

/// The built-in universe: `dungeon-on-dregg`'s real, winnable salt-shore dungeon
/// (the win = the hoard seized, `gold == 500`, and the scene ENDED), plus one honest
/// par completion so a fresh gallery already shows a *verified* board.
///
/// The par run is recorded through the real executor and submitted through the real
/// no-cheat gate — if it did not genuinely win, it simply would not be on the board.
fn seed_registry() -> Registry {
    let mut reg = Registry::new();

    let Ok(dungeon) = Universe::authored(
        "The Salt Shore Descent",
        "dregg (built-in)",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    ) else {
        return reg;
    };

    let id = reg.publish(dungeon.clone());

    // The minimal winning line: take the lantern, descend the gated stair, claim the
    // hoard. Recorded on a real world-cell; accepted only because it really wins.
    if let Ok(play) = record_playthrough(&dungeon, &[0, 0, 0]) {
        let claimed_turns = play.steps.len();
        let _ = reg.submit(Completion {
            universe: id,
            player: "the-house (par)".to_string(),
            play,
            claimed_turns,
        });
    }

    reg
}

// ═══════════════════════════════════════════════════════════════════════════════
// The command logic — pure over a `Registry`, so it is DRIVEN by tests without Discord.
// ═══════════════════════════════════════════════════════════════════════════════

/// A universe as the gallery lists it.
#[derive(Clone, Debug)]
struct UniverseSummary {
    id_hex: String,
    name: String,
    author: String,
    provenance: &'static str,
    /// How many verified completions are on its board.
    entries: usize,
}

/// One verified completion on a leaderboard.
#[derive(Clone, Debug)]
struct BoardEntry {
    rank: usize,
    player: String,
    turns: usize,
    completion_hex: String,
}

/// A universe + its no-cheat leaderboard.
#[derive(Clone, Debug)]
struct UniverseView {
    id_hex: String,
    name: String,
    author: String,
    provenance: &'static str,
    /// Whether a procgen universe still regenerates byte-for-byte from its committed
    /// seed (`None` for an authored universe, where there is no seed to check).
    regenerates: Option<bool>,
    /// The declared win condition, rendered.
    win: String,
    /// How many rooms/passages the world has (a cheap "size" the gallery can show).
    passages: usize,
    board: Vec<BoardEntry>,
}

/// Why a `/gallery play` submission did not land. Every arm is a REAL refusal.
#[derive(Debug)]
enum PlayError {
    /// No universe in the registry matches the given id (or prefix).
    UnknownUniverse,
    /// The `moves` argument did not parse into a move sequence.
    BadMoves(String),
    /// The **real executor refused a move while recording** — e.g. the gated descent
    /// without the lantern. The cheat never even becomes a playthrough.
    RecordRefused(String),
    /// The playthrough recorded, but the registry's no-cheat gate REJECTED it (it did
    /// not re-verify, did not reach the win, or lied about its result).
    Rejected(RejectReason),
}

impl std::fmt::Display for PlayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlayError::UnknownUniverse => {
                write!(
                    f,
                    "no published universe matches that id — try `/gallery list`"
                )
            }
            PlayError::BadMoves(e) => write!(f, "could not read your moves: {e}"),
            PlayError::RecordRefused(e) => write!(
                f,
                "the executor REFUSED one of your moves while replaying it: {e}\n\n\
                 That is the gate doing its job — an illegal move is not a move."
            ),
            PlayError::Rejected(r) => write!(
                f,
                "the leaderboard re-verified your run and rejected it: {r}\n\n\
                 The board only ranks completions that provably reach the win."
            ),
        }
    }
}

/// The full 64-hex content address of a universe (what `list` prints and `show`/`play`
/// accept — a unique prefix is enough).
fn id_hex(id: &UniverseId) -> String {
    id.as_bytes().iter().map(|b| format!("{b:02x}")).collect()
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn provenance_label(p: &Provenance) -> &'static str {
    match p {
        Provenance::Authored => "authored",
        Provenance::Procgen { .. } => "procgen (committed seed)",
    }
}

/// Resolve a user-typed id (a full content address, or any unambiguous prefix of one)
/// to a published universe.
fn find_universe(reg: &Registry, needle: &str) -> Option<UniverseId> {
    let needle = needle.trim().to_ascii_lowercase();
    if needle.is_empty() {
        return None;
    }
    let mut hits = reg
        .universes()
        .map(|u| u.id())
        .filter(|id| id_hex(id).starts_with(&needle));
    let first = hits.next()?;
    // Ambiguous prefix: refuse rather than silently pick one.
    if hits.next().is_some() {
        None
    } else {
        Some(first)
    }
}

/// **LIST** every published universe.
fn list_universes(reg: &Registry) -> Vec<UniverseSummary> {
    reg.universes()
        .map(|u| UniverseSummary {
            id_hex: id_hex(&u.id()),
            name: u.name().to_string(),
            author: u.author().to_string(),
            provenance: provenance_label(u.provenance()),
            entries: reg.leaderboard(u.id()).len(),
        })
        .collect()
}

/// **SHOW** a universe + its no-cheat leaderboard (verified completions, ranked).
fn show_universe(reg: &Registry, needle: &str) -> Option<UniverseView> {
    let id = find_universe(reg, needle)?;
    let u = reg.universe(id)?;

    let win = if u.win().vars.is_empty() {
        "the scene ENDED".to_string()
    } else {
        let vars = u
            .win()
            .vars
            .iter()
            .map(|(k, v)| format!("`{k} == {v}`"))
            .collect::<Vec<_>>()
            .join(" and ");
        format!("the scene ENDED and {vars}")
    };

    let board = reg
        .leaderboard(id)
        .into_iter()
        .enumerate()
        .map(|(i, e)| BoardEntry {
            rank: i + 1,
            player: e.player.clone(),
            turns: e.turns,
            completion_hex: hex32(&e.completion_id),
        })
        .collect();

    Some(UniverseView {
        id_hex: id_hex(&id),
        name: u.name().to_string(),
        author: u.author().to_string(),
        provenance: provenance_label(u.provenance()),
        regenerates: match u.provenance() {
            Provenance::Procgen { .. } => Some(u.regenerates_from_seed()),
            Provenance::Authored => None,
        },
        win: win.clone(),
        passages: u.source().matches("=== ").count(),
        board,
    })
}

/// **PUBLISH** a real procgen universe from a committed seed. The `seed` text is hashed
/// into the 32-byte epoch commitment [`Universe::daily`] derives its verifiable
/// `CommittedSeed` from, so the world is drawn from procgen-dregg's VERIFIED draw stream
/// (never `rand`) and anyone holding the same seed text re-derives the byte-identical
/// world and the identical content address. Publishing is idempotent by content address.
fn publish_universe(
    reg: &mut Registry,
    author: &str,
    seed_text: &str,
) -> Result<UniverseId, String> {
    let epoch: [u8; 32] = *blake3::hash(seed_text.as_bytes()).as_bytes();
    let universe = Universe::daily(author, &epoch).map_err(|e| e.to_string())?;
    Ok(reg.publish(universe))
}

/// **PLAY** — submit a run. The moves are recorded on a REAL, freshly-deployed,
/// identically-seeded world (an illegal move is refused *here*, by the executor), and the
/// resulting receipt chain is handed to the registry's no-cheat gate, which re-executes it
/// from scratch and only ranks it if it provably reaches the win.
///
/// The claimed turn count is bound to the true move count, so a `ResultMismatch` is
/// impossible *from this path* — the tampering the gate defends against is a hand-crafted
/// submission, and the gate still checks it.
fn play_universe(
    reg: &mut Registry,
    needle: &str,
    player: &str,
    moves: &[usize],
) -> Result<Accepted, PlayError> {
    let id = find_universe(reg, needle).ok_or(PlayError::UnknownUniverse)?;
    let universe = reg.universe(id).ok_or(PlayError::UnknownUniverse)?.clone();

    let play = record_playthrough(&universe, moves)
        .map_err(|e| PlayError::RecordRefused(e.to_string()))?;
    let claimed_turns = play.steps.len();

    reg.submit(Completion {
        universe: id,
        player: player.to_string(),
        play,
        claimed_turns,
    })
    .map_err(PlayError::Rejected)
}

/// Parse a `moves` argument: choice indices, comma- and/or space-separated
/// (`"0,0,0"`, `"0 0 0"`, `"0, 0, 0"`).
fn parse_moves(raw: &str) -> Result<Vec<usize>, String> {
    let moves: Result<Vec<usize>, _> = raw
        .split([',', ' ', '\t'])
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|s| {
            s.parse::<usize>()
                .map_err(|_| format!("`{s}` is not a choice index (expected a number like `0`)"))
        })
        .collect();
    let moves = moves?;
    if moves.is_empty() {
        return Err("give at least one move, e.g. `0,0,0`".to_string());
    }
    Ok(moves)
}

// ═══════════════════════════════════════════════════════════════════════════════
// The Discord surface.
// ═══════════════════════════════════════════════════════════════════════════════

/// Register the /gallery command.
pub fn register() -> CreateCommand {
    CreateCommand::new("gallery")
        .description("Browse, publish, and play authored dregg universes (no-cheat leaderboards)")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "list",
            "List every published universe",
        ))
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "show",
                "Show a universe and its verified leaderboard",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "universe",
                    "Universe id (a prefix of the content address is fine)",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "publish",
                "Publish a new procgen universe from a committed seed",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "seed",
                    "Seed text — the same seed always regenerates the same world",
                )
                .required(true),
            ),
        )
        .add_option(
            CreateCommandOption::new(
                CommandOptionType::SubCommand,
                "play",
                "Submit a run — only a verified win is ranked",
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "universe",
                    "Universe id (a prefix of the content address is fine)",
                )
                .required(true),
            )
            .add_sub_option(
                CreateCommandOption::new(
                    CommandOptionType::String,
                    "moves",
                    "Your choice indices, e.g. 0,0,0",
                )
                .required(true),
            ),
        )
}

/// Handle /gallery interactions.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let subcommand = &command.data.options[0].name;

    match subcommand.as_str() {
        "list" => handle_list(ctx, command).await,
        "show" => handle_show(ctx, command).await,
        "publish" => handle_publish(ctx, command).await,
        "play" => handle_play(ctx, command, state).await,
        _ => {}
    }
}

async fn handle_list(ctx: &Context, command: &CommandInteraction) {
    defer_ephemeral(ctx, command).await;

    // Take the registry lock in a tight sync scope — never held across an await.
    let universes = {
        let reg = registry().lock().expect("universe registry lock");
        list_universes(&reg)
    };

    if universes.is_empty() {
        let embed = embeds::dregg_embed("Universe Gallery").description(
            "No universes are published yet. Mint one with `/gallery publish seed:<anything>`.",
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    }

    let mut description = String::new();
    for u in universes.iter().take(10) {
        description.push_str(&format!(
            "**{}** by {}\n{} · {} verified completion(s)\nID: `{}`\n\n",
            u.name,
            u.author,
            u.provenance,
            u.entries,
            &u.id_hex[..16],
        ));
    }
    description.push_str("`/gallery show universe:<id>` for a universe's leaderboard.");

    let embed = embeds::dregg_embed("Universe Gallery")
        .description(description)
        .field("Published", universes.len().to_string(), true);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_show(ctx: &Context, command: &CommandInteraction) {
    let needle = string_option(command, "universe").unwrap_or_default();
    defer_ephemeral(ctx, command).await;

    let view = {
        let reg = registry().lock().expect("universe registry lock");
        show_universe(&reg, &needle)
    };

    let Some(view) = view else {
        let embed = embeds::error_embed(
            "No Such Universe",
            &format!(
                "Nothing published matches `{needle}` (or the prefix is ambiguous).\n\n\
                 Use `/gallery list` to see what's out there."
            ),
        );
        let _ = command
            .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
            .await;
        return;
    };

    let mut board = String::new();
    if view.board.is_empty() {
        board.push_str(
            "No verified completions yet — be the first.\n`/gallery play universe:<id> moves:0,0,0`",
        );
    } else {
        for e in view.board.iter().take(10) {
            board.push_str(&format!(
                "**{}.** {} — **{} turn(s)**\n  completion `{}`\n",
                e.rank,
                e.player,
                e.turns,
                &e.completion_hex[..16],
            ));
        }
        board.push_str(
            "\nEvery entry here **re-verified**: its recorded moves were re-executed on a fresh \
             world and reached the win. Nothing is on this board on its word.",
        );
    }

    let provenance = match view.regenerates {
        Some(true) => format!(
            "{} — regenerates byte-for-byte from its seed",
            view.provenance
        ),
        Some(false) => format!("{} — ⚠ does NOT regenerate from its seed", view.provenance),
        None => view.provenance.to_string(),
    };

    let embed = embeds::dregg_embed(&view.name)
        .description(format!("by **{}**\n\nID: `{}`", view.author, view.id_hex))
        .field("Provenance", provenance, false)
        .field("Win condition", view.win, false)
        .field("Passages", view.passages.to_string(), true)
        .field("Ranked", view.board.len().to_string(), true)
        .field("No-cheat leaderboard", board, false);
    let _ = command
        .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
        .await;
}

async fn handle_publish(ctx: &Context, command: &CommandInteraction) {
    let seed_text = string_option(command, "seed").unwrap_or_default();
    let author = command.user.name.clone();
    defer_ephemeral(ctx, command).await;

    let result = {
        let mut reg = registry().lock().expect("universe registry lock");
        publish_universe(&mut reg, &author, &seed_text).and_then(|id| {
            show_universe(&reg, &id_hex(&id))
                .ok_or_else(|| "published universe vanished".to_string())
        })
    };

    match result {
        Ok(view) => {
            let embed = embeds::success_embed("Universe Published")
                .description(format!(
                    "**{}** by **{}**\n\nID: `{}`",
                    view.name, view.author, view.id_hex
                ))
                .field("Provenance", view.provenance, true)
                .field("Passages", view.passages.to_string(), true)
                .field("Win condition", view.win, false)
                .field(
                    "Content-addressed",
                    "The id is the hash of the world itself. Republishing the same seed is \
                     idempotent, and anyone holding the seed regenerates this exact world.",
                    false,
                )
                .field(
                    "Play it",
                    format!(
                        "`/gallery play universe:{} moves:0,0,0`",
                        &view.id_hex[..16]
                    ),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed(
                "Publish Failed",
                &format!("That seed did not produce a deployable universe: {e}"),
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

async fn handle_play(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let discord_id = command.user.id.get().to_string();
    let user_id = command.user.id.get();
    let player = command.user.name.clone();

    let needle = string_option(command, "universe").unwrap_or_default();
    let raw_moves = string_option(command, "moves").unwrap_or_default();

    defer_ephemeral(ctx, command).await;

    // A run is signed by the player's custodial cclerk (the old bid-signing path,
    // repurposed): the completion is bound to their Discord-derived identity.
    let has_cclerk = match state.db.get_cell_id(&discord_id).await {
        Ok(Some(_)) => true,
        Ok(None) => {
            let embed = embeds::warning_embed(
                "No Cipherclerk",
                "You need a cclerk to submit a run. Use `/cipherclerk create` first.",
            );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
        Err(e) => {
            let embed = embeds::error_embed("Database Error", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };
    debug_assert!(has_cclerk);

    let moves = match parse_moves(&raw_moves) {
        Ok(m) => m,
        Err(e) => {
            let embed = embeds::error_embed("Bad Moves", &PlayError::BadMoves(e).to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
            return;
        }
    };

    let cclerk =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes);
    let signature = sign_run(&cclerk, &needle, &moves);

    let outcome = {
        let mut reg = registry().lock().expect("universe registry lock");
        play_universe(&mut reg, &needle, &player, &moves)
    };

    match outcome {
        Ok(accepted) => {
            let embed = embeds::success_embed("Run Verified — You're On The Board")
                .description(
                    "Your moves were **re-executed on a fresh, identically-seeded world** and they \
                     reached the win. That is why you are ranked — not because you said so.",
                )
                .field("Rank", format!("#{}", accepted.rank), true)
                .field("Turns", accepted.turns.to_string(), true)
                .field(
                    "Completion",
                    format!("`{}`", &hex32(&accepted.completion_id)[..16]),
                    true,
                )
                .field(
                    "Signed by your cclerk",
                    format!("`{}`", &signature[..16.min(signature.len())]),
                    false,
                );
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
        Err(e) => {
            let embed = embeds::error_embed("Run Rejected", &e.to_string());
            let _ = command
                .edit_response(&ctx.http, EditInteractionResponse::new().embed(embed))
                .await;
        }
    }
}

/// Sign a submitted run with the player's cipherclerk (the legacy BLAKE3-MAC wire scheme,
/// `cclerk::sign_legacy` — the same machinery the retired auction-bid path used). The body
/// binds the universe and the exact move sequence:
/// `b"run:" + universe + b":" + each move's le bytes`.
fn sign_run(cclerk: &UserCipherclerk, universe: &str, moves: &[usize]) -> String {
    let mut msg = Vec::new();
    msg.extend_from_slice(b"run:");
    msg.extend_from_slice(universe.as_bytes());
    msg.extend_from_slice(b":");
    for m in moves {
        msg.extend_from_slice(&(*m as u64).to_le_bytes());
    }
    sign_legacy(cclerk, &msg)
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/// Pull a required String sub-option out of the invoked subcommand.
fn string_option(command: &CommandInteraction, name: &str) -> Option<String> {
    let CommandDataOptionValue::SubCommand(opts) = &command.data.options.first()?.value else {
        return None;
    };
    opts.iter()
        .find(|o| o.name == name)
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
}

async fn defer_ephemeral(ctx: &Context, command: &CommandInteraction) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Defer(
                CreateInteractionResponseMessage::new().ephemeral(true),
            ),
        )
        .await;
}

// ═══════════════════════════════════════════════════════════════════════════════
// DRIVEN tests — the command's own logic against the REAL `ugc-dregg` registry.
//
// These call exactly what the handlers call (`list_universes` / `show_universe` /
// `publish_universe` / `play_universe`); the handlers are thin embed-renderers over
// them. Each test owns a fresh `Registry`, so nothing leans on the process-wide one.
// ═══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use dungeon_on_dregg::{CH_CLAIM, CH_DESCEND, CH_LEAVE_LANTERN, CH_TAKE_LANTERN};

    /// A test-owned publish of the real, winnable salt-shore dungeon.
    fn publish_dungeon(reg: &mut Registry) -> UniverseId {
        let u = Universe::authored(
            "The Salt Shore Descent",
            "tester",
            DUNGEON,
            WinCondition::ended_with(&[("gold", 500)]),
        )
        .expect("the built-in dungeon is a deployable universe");
        reg.publish(u)
    }

    /// The generated procgen dungeon is linear: at every room the winning choice is
    /// index 0 (take the key / press onward / descend the gate / seize the hoard).
    fn winning_moves(reg: &Registry, id: UniverseId) -> Vec<usize> {
        let rooms = reg
            .universe(id)
            .expect("published")
            .source()
            .matches("=== room")
            .count();
        vec![0usize; rooms]
    }

    #[test]
    fn the_seeded_gallery_is_not_empty_and_its_par_run_is_verified() {
        // The registry the bot actually boots with.
        let reg = seed_registry();
        let listed = list_universes(&reg);
        assert_eq!(listed.len(), 1, "the built-in dungeon is published");
        assert_eq!(listed[0].name, "The Salt Shore Descent");
        assert_eq!(listed[0].provenance, "authored");
        assert_eq!(
            listed[0].entries, 1,
            "the house's par run is on the board — and it is there only because it \
             re-verified to a real win"
        );

        let view = show_universe(&reg, &listed[0].id_hex).expect("show the built-in universe");
        assert_eq!(view.board.len(), 1);
        assert_eq!(view.board[0].rank, 1);
        assert_eq!(
            view.board[0].turns, 3,
            "the minimal winning line is 3 moves"
        );
        assert!(
            view.win.contains("gold"),
            "the win binds the hoard: {}",
            view.win
        );
    }

    #[test]
    fn publish_then_list_then_leaderboard_end_to_end() {
        let mut reg = Registry::new();
        assert!(list_universes(&reg).is_empty());

        // PUBLISH — a real procgen universe from a committed seed.
        let id = publish_universe(&mut reg, "ember", "gallery-drive-1").expect("publishes");
        let hex = id_hex(&id);

        // LIST — it is there, with its author + provenance.
        let listed = list_universes(&reg);
        assert_eq!(listed.len(), 1);
        assert_eq!(listed[0].author, "ember");
        assert_eq!(listed[0].provenance, "procgen (committed seed)");
        assert_eq!(listed[0].id_hex, hex);
        assert_eq!(listed[0].entries, 0, "a fresh universe has an empty board");

        // The content address is real: the same seed republishes idempotently.
        let again = publish_universe(&mut reg, "ember", "gallery-drive-1").expect("republishes");
        assert_eq!(again, id, "same seed + author ⇒ same content address");
        assert_eq!(list_universes(&reg).len(), 1, "no duplicate was created");

        // ...and a DIFFERENT seed is a different world.
        let other = publish_universe(&mut reg, "ember", "gallery-drive-2").expect("publishes");
        assert_ne!(other, id, "a different seed is a different universe");
        assert_eq!(list_universes(&reg).len(), 2);

        // SHOW — the procgen world regenerates byte-for-byte from its committed seed.
        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.regenerates, Some(true));
        assert!(view.passages >= 4, "the generated dungeon has rooms");

        // PLAY — a REAL winning run against the real executor.
        let moves = winning_moves(&reg, id);
        let accepted =
            play_universe(&mut reg, &hex, "ada", &moves).expect("a real win is accepted");
        assert_eq!(accepted.rank, 1);
        assert_eq!(accepted.turns, moves.len());

        // LEADERBOARD — the verified completion is ranked.
        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.board.len(), 1);
        assert_eq!(view.board[0].player, "ada");
        assert_eq!(view.board[0].rank, 1);
        assert_eq!(view.board[0].turns, moves.len());
        assert_eq!(list_universes(&reg)[0].entries, 1);

        // A prefix of the content address resolves too (what a user actually types).
        assert!(show_universe(&reg, &hex[..16]).is_some());
    }

    #[test]
    fn a_cheat_run_is_rejected_and_never_touches_the_board() {
        let mut reg = Registry::new();
        let id = publish_dungeon(&mut reg);
        let hex = id_hex(&id);

        // An honest win first, so the board is non-empty and we can prove the cheat
        // changes nothing.
        let honest = play_universe(
            &mut reg,
            &hex,
            "ada",
            &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM],
        )
        .expect("the honest 3-move win is accepted");
        assert_eq!(honest.turns, 3);

        // THE CHEAT: skip the lantern, then try the gated descent. The gate
        // (`has_lantern >= 1`) is a real executor `StateConstraint`, not app code — so
        // the move is REFUSED on replay and the run never becomes a completion.
        let cheat = play_universe(
            &mut reg,
            &hex,
            "mallory",
            &[CH_LEAVE_LANTERN, CH_DESCEND, CH_CLAIM],
        );
        assert!(
            matches!(
                cheat,
                Err(PlayError::RecordRefused(_)) | Err(PlayError::Rejected(_))
            ),
            "a keyless descent must be REFUSED, got {cheat:?}"
        );

        // AN INCOMPLETE RUN: real moves, but it never reaches the win. The board
        // rejects it explicitly.
        let partial = play_universe(&mut reg, &hex, "quinn", &[CH_TAKE_LANTERN]);
        assert!(
            matches!(partial, Err(PlayError::Rejected(RejectReason::DidNotWin))),
            "an incomplete run must be rejected as DidNotWin, got {partial:?}"
        );

        // Non-vacuous: NEITHER cheat landed. Only ada is ranked.
        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.board.len(), 1, "no cheat entry landed");
        assert_eq!(view.board[0].player, "ada");
    }

    #[test]
    fn the_board_ranks_by_turns_and_a_slower_real_win_still_counts() {
        let mut reg = Registry::new();
        let id = publish_dungeon(&mut reg);
        let hex = id_hex(&id);

        // bran plays first, but takes a detour (retreat to the shore and back) — a REAL
        // win, just a slower one: 5 moves.
        let bran = play_universe(
            &mut reg,
            &hex,
            "bran",
            &[
                CH_TAKE_LANTERN,
                dungeon_on_dregg::CH_RETREAT,
                CH_TAKE_LANTERN,
                CH_DESCEND,
                CH_CLAIM,
            ],
        )
        .expect("a slower but real win is still accepted");
        assert_eq!(bran.turns, 5);
        assert_eq!(bran.rank, 1, "first on an empty board");

        // ada then plays the minimal line and takes the top slot.
        let ada = play_universe(
            &mut reg,
            &hex,
            "ada",
            &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM],
        )
        .expect("the minimal win is accepted");
        assert_eq!(ada.turns, 3);
        assert_eq!(ada.rank, 1, "fewer turns takes rank 1");

        let view = show_universe(&reg, &hex).expect("show");
        assert_eq!(view.board.len(), 2);
        assert_eq!(view.board[0].player, "ada");
        assert_eq!(view.board[0].turns, 3);
        assert_eq!(view.board[1].player, "bran");
        assert_eq!(view.board[1].turns, 5);
    }

    #[test]
    fn an_unknown_universe_and_bad_moves_are_honest_refusals() {
        let mut reg = Registry::new();
        publish_dungeon(&mut reg);

        assert!(show_universe(&reg, "deadbeef").is_none());
        assert!(matches!(
            play_universe(&mut reg, "deadbeef", "nobody", &[0]),
            Err(PlayError::UnknownUniverse)
        ));

        assert!(parse_moves("").is_err());
        assert!(parse_moves("north").is_err());
        assert_eq!(parse_moves("0,0,0").unwrap(), vec![0, 0, 0]);
        assert_eq!(parse_moves("0 1  2").unwrap(), vec![0, 1, 2]);

        // An out-of-range choice index is refused by the real executor, not by a
        // bounds-check we wrote.
        let hex = list_universes(&reg)[0].id_hex.clone();
        let out = play_universe(&mut reg, &hex, "confused", &[99]);
        assert!(
            matches!(out, Err(PlayError::RecordRefused(_))),
            "an impossible choice is refused by the executor, got {out:?}"
        );
    }
}
