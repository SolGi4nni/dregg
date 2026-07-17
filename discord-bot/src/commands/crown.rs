//! 👑 `/crown` — **fold a finished match to ONE proof: prove you won without revealing how.**
//!
//! THE CROWN, wired. A finished `/play tug` or `/play automatafl` match — every turn of it a
//! real committed executor turn — FOLDS, in the background, into ONE succinct
//! `WholeChainProof`, and that proof (never the moves) is submitted to the proof-carrying
//! game board:
//!
//! ```text
//!   PLAY (Discord, fast)      PROVE (background, minutes)      SUBMIT (a proof, not moves)
//!   ────────────────────      ───────────────────────────      ───────────────────────────
//!   /play tug|automatafl  ─▶  dreggnet_prove_service        ─▶ dreggnet_game_board::GameBoard
//!   a win lands           👑  ::enqueue → the deployed          ::submit — verified in O(1),
//!   "Fold this match"         recursive STARK fold              ranked, has_moves() == false
//! ```
//!
//! * **the fold is real and slow** — [`dreggnet_prove_service::MatchProveService`] runs the
//!   deployed recursion (`prove_turn_chain_recursive`) on a bounded worker pool, OFF the
//!   interaction path. The player gets an honest "proving in the background (minutes)" status
//!   they poll; nothing spins, nothing pretends.
//! * **the board stores NO moves** — an accepted entry is the proof envelope + the attested
//!   publics ([`ugc_dregg`] proof path). For a tug match the fold's leaves are Poseidon2
//!   membership proofs whose public inputs are `[blinded_leaf, hand_root]` — the winner's
//!   card ids are in NOBODY's hands but their own.
//! * **any stranger re-verifies in O(1)** — the proof envelope is attached to the ranked post
//!   as a file, and a **Re-verify** button lets ANY user watch this bot re-run the whole-history
//!   light client against the pinned anchor: one check, zero replay, zero trust in the winner
//!   — or in this bot.
//!
//! ## Honest scope
//!
//! * The deployed STARK is *succinct*, not *hiding*: "moves never posted" is a
//!   data-availability privacy property (the board never sees them, nobody publishes them),
//!   NOT a crypto-ZK claim about the transcript. The footer says so.
//! * The **tug** fold consumes the winner's real private match record (dealt hand + ordered
//!   plays + the terminal win), read through `TugSession`'s owner-facing match-record seam.
//! * The **automatafl** fold is the game crate's own named scope: the committed D1
//!   automaton-step chain (as many turns as the match resolved, stepping from the final
//!   committed position) — the player-move D2/D3 stages fold identically but are not the
//!   chain driven here ([`dreggnet_game_board`]'s named residual, repeated in the post).
//! * The board + fold records live in this process (an in-memory `GameBoard`), like the other
//!   offering sessions; a restart forgets pending folds. The proof FILE survives on Discord —
//!   and stays verifiable by anyone holding the anchor.
//!
//! ## The custom-id wire
//!
//! | id                       | meaning                                                    |
//! |--------------------------|------------------------------------------------------------|
//! | `crown:fold:<key>`       | fold this channel's finished `<key>` match (enqueue)       |
//! | `crown:status:<token>`   | poll the background fold; on Ready, submit + post the crown |
//! | `crown:reverify:<token>` | ANY user: re-run the O(1) light client on the ranked entry  |
//!
//! `main.rs` routes every `crown:` press here (see the Repair registration lines in the
//! integration report); the win-moment offer is posted by `commands::offering`'s ended-match
//! hook calling [`offer_fold`].

use std::collections::HashMap;
use std::sync::OnceLock;
use std::sync::mpsc::{SyncSender, sync_channel};

use serenity::all::{
    ButtonStyle, ChannelId, CommandDataOptionValue, CommandInteraction, CommandOptionType,
    ComponentInteraction, Context, CreateActionRow, CreateAttachment, CreateButton, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateEmbedFooter, CreateInteractionResponse,
    CreateInteractionResponseMessage, CreateMessage,
};

use dregg_automatafl::AutomataflOffering;
use dreggnet_game_board::{Game, GameBoard, MatchProof, UniverseId, match_anchor};
use dreggnet_prove_service::{
    AutomataflMatch, JobId, JobStatus, MatchProveService, PlayedMatch, match_prove_service,
};

use crate::BotState;
use crate::commands::offering::{self, identity_of, truncate};

/// The custom-id namespace every crown press lives in (`main.rs` routes on `crown:`).
pub const PREFIX: &str = "crown";

/// The embed colour — gold, obviously.
const COLOR: u32 = 0xD4A017;
/// The refusal colour.
const COLOR_REFUSED: u32 = 0xE63946;

/// The honest one-line scope footer every crown embed carries.
const SCOPE_FOOTER: &str = "succinct STARK fold · O(1) stranger verify · privacy = the moves are \
     never posted (data-availability, not crypto-ZK of the transcript)";

/// Whether an offering key has a crown (a proof-carrying board behind it). The hook in the
/// generic offering adapter calls this on a landed `ended: true` turn.
pub fn foldable_key(key: &str) -> bool {
    matches!(key, "tug" | "automatafl")
}

/// The [`Game`] an offering key folds into, if any.
fn game_of_key(key: &str) -> Option<Game> {
    match key {
        "tug" => Some(Game::MultiwayTug),
        "automatafl" => Some(Game::Automatafl),
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The crown core — ONE owner thread holding the proving service + the board.
//
// The same confinement pattern as `offering::Store`: the `GameBoard` (and the fold records)
// are built on, and never leave, a dedicated thread; every access is a Send job shipped there
// and awaited. The proving service's own workers do the slow folds; jobs here are short
// (an enqueue, a status read, one O(1) verify on submit).
// ─────────────────────────────────────────────────────────────────────────────

/// A ranked fold's board facts (everything a re-verify or a status re-read needs).
#[derive(Clone)]
struct Ranked {
    /// The board universe this fold was ranked in (pinned to THIS fold's anchor).
    universe: UniverseId,
    /// The accepted entry's content id — the re-verify key.
    completion_id: [u8; 32],
    /// The attested turn count (the rank key).
    turns: usize,
    /// The 1-based rank at insertion.
    rank: usize,
    /// The proof envelope's size in bytes (for the honest "this is the WHOLE match" line).
    proof_len: usize,
    /// The root-circuit VK fingerprint prefix (hex), the anchor's trust root.
    vk8: String,
}

/// One tracked fold: which game, whose, where, and how far along.
struct FoldRecord {
    game: Game,
    /// The Discord channel the match was played in.
    channel: u64,
    /// The submitting player — their derived dregg identity hex (never a nickname).
    player: String,
    /// The background proving job.
    job: JobId,
    /// `Some` once the proof was submitted to (and accepted by) the board.
    ranked: Option<Ranked>,
}

/// The owner thread's state: the REAL background prover, the proof-carrying board, the folds.
struct CrownCore {
    service: MatchProveService,
    board: GameBoard,
    folds: HashMap<u64, FoldRecord>,
    next_token: u64,
}

type CrownJob = Box<dyn FnOnce(&mut CrownCore) + Send + 'static>;

struct Crown {
    jobs: SyncSender<CrownJob>,
}

fn crown() -> &'static Crown {
    static CROWN: OnceLock<Crown> = OnceLock::new();
    CROWN.get_or_init(|| {
        let (jobs, rx) = sync_channel::<CrownJob>(64);
        std::thread::Builder::new()
            .name("crown-board".into())
            .spawn(move || {
                // Built HERE, lives HERE: the production match-fold pool (bounded workers,
                // `DREGG_MATCH_PROVE_WORKERS`/`_QUEUE_DEPTH`) + the proof-carrying board.
                let mut core = CrownCore {
                    service: match_prove_service(),
                    board: GameBoard::new(),
                    folds: HashMap::new(),
                    next_token: 1,
                };
                while let Ok(job) = rx.recv() {
                    job(&mut core);
                }
            })
            .expect("spawn the crown board thread");
        Crown { jobs }
    })
}

/// Run `f` on the crown's owner thread and hand back its result.
fn run<R: Send + 'static>(f: impl FnOnce(&mut CrownCore) -> R + Send + 'static) -> R {
    let (tx, rx) = sync_channel::<R>(1);
    crown()
        .jobs
        .send(Box::new(move |core| {
            let _ = tx.send(f(core));
        }))
        .expect("the crown board thread is alive");
    rx.recv().expect("the crown board thread answered")
}

// ─────────────────────────────────────────────────────────────────────────────
// The sync core — enqueue / poll(+submit) / re-verify / board read.
// ─────────────────────────────────────────────────────────────────────────────

/// The result of asking to fold a match.
enum Enqueued {
    /// Accepted — poll this token.
    Token(u64),
    /// This channel's match already has a live (unranked) fold — poll that one.
    Already(u64),
    /// The bounded proving queue is full (the play already happened; try again shortly).
    QueueFull,
}

/// Enqueue a played match for the background fold (guarding against a duplicate live fold of
/// the same channel+game).
fn enqueue_fold(game: Game, channel: u64, player: String, m: PlayedMatch) -> Enqueued {
    run(move |core| {
        if let Some((&t, _)) = core
            .folds
            .iter()
            .find(|(_, r)| r.channel == channel && r.game == game && r.ranked.is_none())
        {
            return Enqueued::Already(t);
        }
        match core.service.enqueue(m) {
            None => Enqueued::QueueFull,
            Some(job) => {
                let token = core.next_token;
                core.next_token += 1;
                core.folds.insert(
                    token,
                    FoldRecord {
                        game,
                        channel,
                        player,
                        job,
                        ranked: None,
                    },
                );
                Enqueued::Token(token)
            }
        }
    })
}

/// A status poll's outcome.
enum Poll {
    NoSuchFold,
    /// Still in the pool — `proving` says a worker has picked it up; the counters are the
    /// pool's honest gauges.
    Pending {
        proving: bool,
        in_flight: u64,
        workers: usize,
    },
    /// The fold itself refused the match (or the prover errored). Honest and terminal.
    Failed(String),
    /// The fold JUST completed: the proof was submitted to the board and ranked NOW. Carries
    /// the envelope bytes exactly once, for the attached file.
    JustRanked {
        game: Game,
        facts: Ranked,
        proof_bytes: Vec<u8>,
    },
    /// Ranked earlier — the board still holds it (press Re-verify on the crown post).
    AlreadyRanked {
        game: Game,
        facts: Ranked,
    },
    /// The fold finished but the board REFUSED the proof — a prover/board mismatch, surfaced
    /// honestly (nothing was ranked).
    BoardRefused(String),
}

/// Poll a fold; when the background job is `Done`, pin the board to this fold's anchor,
/// submit the proof (the O(1) accept path), and rank it.
fn poll_fold(token: u64) -> Poll {
    run(move |core| {
        let Some(rec) = core.folds.get(&token) else {
            return Poll::NoSuchFold;
        };
        if let Some(facts) = rec.ranked.clone() {
            return Poll::AlreadyRanked {
                game: rec.game,
                facts,
            };
        }
        let (game, player, job) = (rec.game, rec.player.clone(), rec.job);
        match core.service.status(job) {
            s @ (JobStatus::Queued | JobStatus::Proving) => {
                let m = core.service.metrics();
                Poll::Pending {
                    proving: matches!(s, JobStatus::Proving),
                    in_flight: m.in_flight,
                    workers: core.service.workers(),
                }
            }
            JobStatus::Failed(e) => Poll::Failed(e),
            JobStatus::Unknown => Poll::Failed(
                "the proving pool does not know this job (dropped on a full queue?)".to_string(),
            ),
            JobStatus::Done(p) => {
                let proof: MatchProof = (*p).clone();
                // Pin the board's trust anchor from THIS honest fold (the setup-party mint:
                // VK + genesis + WIN roots), publish the game's board universe against it,
                // then hand the board the proof — which it verifies in O(1), re-witnessing
                // nothing, and ranks. A forged envelope would be REFUSED right here.
                let universe = core.board.open(game, match_anchor(&proof));
                match core.board.submit(game, &player, &proof) {
                    Err(e) => Poll::BoardRefused(e.to_string()),
                    Ok(accepted) => {
                        let facts = Ranked {
                            universe,
                            completion_id: accepted.completion_id,
                            turns: accepted.turns,
                            rank: accepted.rank,
                            proof_len: proof.proof_bytes.len(),
                            vk8: hex::encode(&proof.vk.0[..4]),
                        };
                        if let Some(rec) = core.folds.get_mut(&token) {
                            rec.ranked = Some(facts.clone());
                        }
                        Poll::JustRanked {
                            game,
                            facts,
                            proof_bytes: proof.proof_bytes,
                        }
                    }
                }
            }
        }
    })
}

/// **Independently re-verify** a ranked fold — re-run the O(1) whole-history light client on
/// the STORED proof against the pinned anchor. Never a replay: the moves were never posted.
/// Returns the re-attested turn count. Any user may call this; that is the point.
fn reverify_fold(token: u64) -> Result<(Game, usize, Ranked), String> {
    run(move |core| {
        let Some(rec) = core.folds.get(&token) else {
            return Err("no such fold".to_string());
        };
        let Some(facts) = rec.ranked.clone() else {
            return Err("this fold is not ranked yet — poll its proving status first".to_string());
        };
        core.board
            .registry()
            .reverify_entry(facts.universe, &facts.completion_id)
            .map(|turns| (rec.game, turns, facts))
            .map_err(|why| format!("the light client REFUSED the stored proof: {why}"))
    })
}

/// The board read for `/crown board`: per game, the ranked entry lines + the
/// stores-no-moves assertion (asserted alongside non-emptiness, per the API's own note).
fn board_lines(game: Game) -> (Vec<String>, bool) {
    run(move |core| {
        let lines: Vec<String> = core
            .board
            .leaderboard(game)
            .iter()
            .enumerate()
            .map(|(i, e)| {
                format!(
                    "**#{}** `{}…` — {} turns attested · proof-backed: {} · moves stored: **{}**",
                    i + 1,
                    &e.player[..e.player.len().min(12)],
                    e.turns,
                    e.is_proof_backed(),
                    e.has_moves(),
                )
            })
            .collect();
        let no_moves = core.board.stores_no_moves(game);
        (lines, no_moves)
    })
}

/// The channel's folds + a live one-word status each (for `/crown status`).
fn folds_in(channel: u64) -> Vec<(u64, Game, String)> {
    run(move |core| {
        let mut rows: Vec<(u64, Game, String)> = core
            .folds
            .iter()
            .filter(|(_, r)| r.channel == channel)
            .map(|(&t, r)| {
                let status = if r.ranked.is_some() {
                    "RANKED — the board holds the proof (and no moves)".to_string()
                } else {
                    match core.service.status(r.job) {
                        JobStatus::Queued => "queued".to_string(),
                        JobStatus::Proving => "proving (the real fold — minutes)".to_string(),
                        JobStatus::Done(_) => {
                            "proof READY — press its status button to rank it".to_string()
                        }
                        JobStatus::Failed(e) => format!("failed: {}", truncate(&e, 120)),
                        JobStatus::Unknown => "unknown".to_string(),
                    }
                };
                (t, r.game, status)
            })
            .collect();
        rows.sort_by_key(|(t, _, _)| *t);
        rows
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Extracting the played match from the live `/play` session.
// ─────────────────────────────────────────────────────────────────────────────

/// The channel's finished automatafl match as a fold job. Honest scope (the game-board crate's
/// own named residual): the folded chain is the committed **D1 automaton-step** chain — as many
/// turns as the match resolved, stepping from the final committed position — not the D2/D3
/// player-move stages (which lower identically but are not the chain driven here).
fn played_automatafl(channel: u64) -> Option<PlayedMatch> {
    offering::with_live::<AutomataflOffering, _>(channel, |live| {
        if !live.session.ended() {
            return None;
        }
        Some(PlayedMatch::Automatafl(AutomataflMatch {
            start: live.session.board().clone(),
            turns: live.session.turn_no().max(1) as usize,
        }))
    })
    .flatten()
}

/// The channel's finished, WON match of `game` (tug reads the winner's private match record
/// through `commands::portfolio::played_tug_match` — the seam with private access to the seated
/// session), or `None` when there is nothing crowned to fold here yet.
fn played_match_of(game: Game, channel: u64) -> Option<PlayedMatch> {
    match game {
        Game::MultiwayTug => crate::commands::portfolio::played_tug_match(channel),
        Game::Automatafl => played_automatafl(channel),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The Discord surface — the offer, the command, the buttons.
// ─────────────────────────────────────────────────────────────────────────────

fn fold_button(key: &str) -> CreateActionRow {
    CreateActionRow::Buttons(vec![
        CreateButton::new(format!("{PREFIX}:fold:{key}"))
            .label("👑 Fold this match to one proof")
            .style(ButtonStyle::Primary),
    ])
}

fn status_button(token: u64) -> CreateActionRow {
    CreateActionRow::Buttons(vec![
        CreateButton::new(format!("{PREFIX}:status:{token}"))
            .label("Proving status")
            .style(ButtonStyle::Secondary),
    ])
}

fn reverify_button(token: u64) -> CreateActionRow {
    CreateActionRow::Buttons(vec![
        CreateButton::new(format!("{PREFIX}:reverify:{token}"))
            .label("Re-verify (anyone, O(1))")
            .style(ButtonStyle::Success),
    ])
}

fn crown_embed(title: &str, body: &str) -> CreateEmbed {
    CreateEmbed::new()
        .title(title)
        .description(truncate(body, 4000))
        .color(COLOR)
        .footer(CreateEmbedFooter::new(SCOPE_FOOTER))
}

/// **The win-moment offer** — posted by the generic offering adapter the moment a tug /
/// automatafl match ENDS on a landed turn (the Repair-applied hook in
/// `commands::offering::handle_component`). Public, in-channel, one button.
pub async fn offer_fold(ctx: &Context, channel_id: ChannelId, key: &str) {
    if !foldable_key(key) {
        return;
    }
    let body = "This match is over — and every move of it is already a committed, verified \
        turn. Press the button and the whole match FOLDS, in the background, into **one \
        succinct proof**.\n\n\
        The proof goes on the game's board. The moves do not — **your hand was fog to your \
        opponent and it stays fog forever**: the board stores the proof and *nothing else*, \
        and any stranger can re-check the entire match in **O(1)** — one light-client \
        verification, no replay, no trusting you, no trusting this bot.\n\n\
        *Prove you won. Reveal nothing about how.*";
    let msg = CreateMessage::new()
        .embed(crown_embed(
            "👑 Prove you won — without revealing how",
            body,
        ))
        .components(vec![fold_button(key)]);
    let _ = channel_id.send_message(&ctx.http, msg).await;
}

/// Register `/crown <action>` — fold the channel's finished match / poll folds / read the board.
pub fn register() -> CreateCommand {
    let mut action = CreateCommandOption::new(
        CommandOptionType::String,
        "action",
        "fold the finished match · status of this channel's folds · the proof board",
    )
    .required(true);
    for a in ["fold", "status", "board"] {
        action = action.add_string_choice(a, a);
    }
    CreateCommand::new("crown")
        .description("Fold a finished match into ONE proof — prove you won without revealing how")
        .add_option(action)
}

/// The enqueue tail shared by the slash `fold` and the offer button: build the honest
/// "proving in the background" response (or the honest refusal).
fn enqueue_response(
    game: Game,
    channel: u64,
    player_hex: String,
) -> (CreateEmbed, Vec<CreateActionRow>) {
    let Some(m) = played_match_of(game, channel) else {
        return (
            CreateEmbed::new()
                .title("Nothing crowned to fold here")
                .description(format!(
                    "No finished, WON `{}` match is live in this channel. Win one — \
                     `/play {}` — and the crown appears.",
                    game.slug(),
                    game.slug(),
                ))
                .color(COLOR_REFUSED),
            Vec::new(),
        );
    };
    // The deployed win leaf proves the INFLUENCE path (`charm >= 11`, the range gadget). A tug
    // round can also be won on the guild-count threshold with charm below 11 — that win is real
    // on the executor, but the fold's win leaf cannot honestly attest it, and handing it to the
    // prover would trip the witness builder. Refuse HERE, honestly, rather than forge or wedge.
    if let PlayedMatch::Tug(t) = &m
        && let Some(w) = t.win
        && w.charm < 11
    {
        return (
            CreateEmbed::new()
                .title("This win folds no crown (yet)")
                .description(format!(
                    "The round was won on the **guild threshold** (charm {} < 11). The deployed \
                     whole-match win leaf proves the *influence* path (`charm >= 11`) — so this \
                     match is refused rather than mis-attested. Win on influence and the crown \
                     folds.",
                    w.charm,
                ))
                .color(COLOR_REFUSED),
            Vec::new(),
        );
    }
    match enqueue_fold(game, channel, player_hex, m) {
        Enqueued::Token(token) => (
            crown_embed(
                &format!("👑 Fold #{token} enqueued — proving in the background"),
                &format!(
                    "The **{}** match is now folding into one `WholeChainProof` on the \
                     background prover pool. This is the real recursive STARK fold — it takes \
                     **minutes**, not milliseconds, and nothing here waits on it: the play is \
                     already over and committed.\n\n\
                     Press **Proving status** to poll. When the proof is ready it goes to the \
                     board — the proof, never the moves.",
                    game.title(),
                ),
            ),
            vec![status_button(token)],
        ),
        Enqueued::Already(token) => (
            crown_embed(
                &format!("Fold #{token} is already running for this match"),
                "One fold per match at a time — poll the one in flight.",
            ),
            vec![status_button(token)],
        ),
        Enqueued::QueueFull => (
            CreateEmbed::new()
                .title("The proving queue is full")
                .description(
                    "The bounded background pool refused a new job (drop, not block — the \
                     play already happened and loses nothing). Try again in a minute.",
                )
                .color(COLOR_REFUSED),
            Vec::new(),
        ),
    }
}

/// The ranked crown post: embed + re-verify button + (on first rank) the proof envelope file.
fn ranked_post(game: Game, token: u64, facts: &Ranked) -> (CreateEmbed, Vec<CreateActionRow>) {
    let scope_line = match game {
        Game::MultiwayTug => {
            "The folded leaves are blinded Poseidon2 membership proofs — the proof's public \
             inputs are `[blinded_leaf, hand_root]`. **The winning hand was never revealed and \
             is not in this proof.**"
        }
        Game::Automatafl => {
            "The folded chain is the committed D1 automaton-step chain (the game crate's named \
             scope for the match fold) — the board transitions are proven; **no move list is \
             posted anywhere**."
        }
    };
    let body = format!(
        "**{turns} turns attested** · rank **#{rank}** · proof envelope **{len} bytes** · \
         vk `{vk}…` · completion `{cid}…`\n\n\
        The board verified this proof in **O(1)** — one whole-history light-client check \
        against its pinned anchor (VK + genesis + WIN). It re-witnessed nothing, replayed \
        nothing, and stored **no moves**: `has_moves() == false` on every entry.\n\n\
        {scope}\n\n\
        The envelope is attached. **Anyone** may press *Re-verify* and watch this bot re-run \
        the same O(1) check on the stored proof, in public — or take the file and check it \
        themselves. You do not have to trust the winner. You do not have to trust this bot.",
        turns = facts.turns,
        rank = facts.rank,
        len = facts.proof_len,
        vk = facts.vk8,
        cid = hex::encode(&facts.completion_id[..4]),
        scope = scope_line,
    );
    (
        crown_embed(
            &format!(
                "👑 RANKED — the board holds a proof and NO moves ({} · fold #{token})",
                game.title()
            ),
            &body,
        ),
        vec![reverify_button(token)],
    )
}

/// Route `/crown <action>`.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let action = command
        .data
        .options
        .first()
        .and_then(|o| match &o.value {
            CommandDataOptionValue::String(s) => Some(s.clone()),
            _ => None,
        })
        .unwrap_or_default();
    let channel = command.channel_id.get();

    match action.as_str() {
        "fold" => {
            // Whichever crowned game has a finished, won match live in this channel.
            let game = [Game::MultiwayTug, Game::Automatafl]
                .into_iter()
                .find(|g| played_match_of(*g, channel).is_some());
            let Some(game) = game else {
                respond_ephemeral(
                    ctx,
                    command,
                    "No finished, WON match is live in this channel. Win a `/play tug` or \
                     `/play automatafl` match first — then fold it to one proof.",
                )
                .await;
                return;
            };
            let player = identity_of(state, command.user.id.get()).0;
            let (embed, rows) = enqueue_response(game, channel, player);
            respond_embed(ctx, command, embed, rows, false).await;
        }
        "status" => {
            let rows = folds_in(channel);
            let body = if rows.is_empty() {
                "No folds in this channel yet. Win a match, then `/crown fold`.".to_string()
            } else {
                rows.iter()
                    .map(|(t, g, s)| format!("**fold #{t}** ({}) — {s}", g.slug()))
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            let buttons: Vec<CreateActionRow> = rows
                .iter()
                .take(5)
                .map(|(t, _, _)| status_button(*t))
                .collect();
            respond_embed(
                ctx,
                command,
                crown_embed("👑 This channel's match folds", &body),
                buttons,
                true,
            )
            .await;
        }
        "board" => {
            let mut body = String::new();
            for game in [Game::MultiwayTug, Game::Automatafl] {
                let (lines, no_moves) = board_lines(game);
                body.push_str(&format!("**{}**\n", game.title()));
                if lines.is_empty() {
                    body.push_str("_no ranked proofs yet_\n");
                } else {
                    body.push_str(&lines.join("\n"));
                    body.push('\n');
                    body.push_str(&format!(
                        "every entry proof-backed with NO moves stored: **{no_moves}**\n"
                    ));
                }
                body.push('\n');
            }
            respond_embed(
                ctx,
                command,
                crown_embed("👑 The proof-carrying game board", body.trim_end()),
                Vec::new(),
                false,
            )
            .await;
        }
        other => {
            respond_ephemeral(ctx, command, &format!("Unknown crown action `{other}`.")).await;
        }
    }
}

/// Route a `crown:` component press (`main.rs` sends every `crown:` custom-id here).
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.clone();
    let parts: Vec<&str> = id.split(':').collect();
    let channel = component.channel_id.get();

    match parts.as_slice() {
        [PREFIX, "fold", key] => {
            let Some(game) = game_of_key(key) else {
                return;
            };
            let player = identity_of(state, component.user.id.get()).0;
            let (embed, rows) = enqueue_response(game, channel, player);
            // Replace the offer message (its button has done its job; no double-enqueue bait).
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::UpdateMessage(
                        CreateInteractionResponseMessage::new()
                            .embed(embed)
                            .components(rows),
                    ),
                )
                .await;
        }
        [PREFIX, "status", tok] => {
            let Ok(token) = tok.parse::<u64>() else {
                return;
            };
            match poll_fold(token) {
                Poll::NoSuchFold => {
                    component_ephemeral(
                        ctx,
                        component,
                        "No such fold (the bot may have restarted — pending folds are \
                         in-process; re-fold the match with `/crown fold`).",
                    )
                    .await;
                }
                Poll::Pending {
                    proving,
                    in_flight,
                    workers,
                } => {
                    let phase = if proving {
                        "a worker is FOLDING it now"
                    } else {
                        "queued for a worker"
                    };
                    component_ephemeral(
                        ctx,
                        component,
                        &format!(
                            "⏳ **Fold #{token}: proving in the background** — {phase} \
                             ({in_flight} fold(s) in flight on {workers} worker(s)). The real \
                             recursive fold takes minutes; press again later. Nothing is \
                             waiting on it — the match is already committed.",
                        ),
                    )
                    .await;
                }
                Poll::Failed(e) => {
                    component_ephemeral(
                        ctx,
                        component,
                        &format!(
                            "✗ **Fold #{token} failed — nothing was ranked.** The fold's own \
                             teeth: {e}",
                        ),
                    )
                    .await;
                }
                Poll::BoardRefused(e) => {
                    component_ephemeral(
                        ctx,
                        component,
                        &format!(
                            "✗ **The board REFUSED fold #{token}'s proof — nothing was \
                             ranked.** {e}",
                        ),
                    )
                    .await;
                }
                Poll::JustRanked {
                    game,
                    facts,
                    proof_bytes,
                } => {
                    let (embed, rows) = ranked_post(game, token, &facts);
                    let file = CreateAttachment::bytes(
                        proof_bytes,
                        format!("{}-match-fold-{token}.dreggproof", game.slug()),
                    );
                    // PUBLIC — the crown moment belongs to the channel.
                    let _ = component
                        .create_response(
                            &ctx.http,
                            CreateInteractionResponse::Message(
                                CreateInteractionResponseMessage::new()
                                    .embed(embed)
                                    .components(rows)
                                    .add_file(file),
                            ),
                        )
                        .await;
                }
                Poll::AlreadyRanked { game, facts } => {
                    component_ephemeral(
                        ctx,
                        component,
                        &format!(
                            "👑 Fold #{token} ({}) is already RANKED — {} turns attested, \
                             rank #{}. Press **Re-verify** on its crown post (or run \
                             `/crown board`).",
                            game.slug(),
                            facts.turns,
                            facts.rank,
                        ),
                    )
                    .await;
                }
            }
        }
        [PREFIX, "reverify", tok] => {
            let Ok(token) = tok.parse::<u64>() else {
                return;
            };
            // PUBLIC on both arms — the whole point is that everyone watches the check run.
            let (embed, rows) = match reverify_fold(token) {
                Ok((game, turns, facts)) => (
                    crown_embed(
                        &format!("✓ Re-verified in O(1) — fold #{token} ({})", game.slug()),
                        &format!(
                            "The whole-history light client just re-checked the **stored** \
                             proof against the board's pinned anchor: **{turns} turns \
                             attested**, genesis → WIN, completion `{}…`.\n\n\
                             No move was replayed. None exists to replay — the board stores \
                             the proof and nothing else. That is the crown: *anyone* can do \
                             what just happened, in one cheap check, forever.",
                            hex::encode(&facts.completion_id[..4]),
                        ),
                    ),
                    vec![reverify_button(token)],
                ),
                Err(e) => (
                    CreateEmbed::new()
                        .title(format!("✗ Re-verify refused — fold #{token}"))
                        .description(truncate(&e, 2000))
                        .color(COLOR_REFUSED),
                    Vec::new(),
                ),
            };
            let _ = component
                .create_response(
                    &ctx.http,
                    CreateInteractionResponse::Message(
                        CreateInteractionResponseMessage::new()
                            .embed(embed)
                            .components(rows),
                    ),
                )
                .await;
        }
        _ => {}
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Small response helpers.
// ─────────────────────────────────────────────────────────────────────────────

async fn respond_embed(
    ctx: &Context,
    command: &CommandInteraction,
    embed: CreateEmbed,
    rows: Vec<CreateActionRow>,
    ephemeral: bool,
) {
    let mut msg = CreateInteractionResponseMessage::new().embed(embed);
    if !rows.is_empty() {
        msg = msg.components(rows);
    }
    if ephemeral {
        msg = msg.ephemeral(true);
    }
    let _ = command
        .create_response(&ctx.http, CreateInteractionResponse::Message(msg))
        .await;
}

async fn respond_ephemeral(ctx: &Context, command: &CommandInteraction, text: &str) {
    let _ = command
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(text)
                    .ephemeral(true),
            ),
        )
        .await;
}

async fn component_ephemeral(ctx: &Context, component: &ComponentInteraction, text: &str) {
    let _ = component
        .create_response(
            &ctx.http,
            CreateInteractionResponse::Message(
                CreateInteractionResponseMessage::new()
                    .content(text)
                    .ephemeral(true),
            ),
        )
        .await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the wire + the key gate (pure; the fold pipeline is the upstream crates' own
// driven scope, and a real fold is minutes of STARK recursion — not a unit test).
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_the_two_portfolio_games_are_crowned() {
        assert!(foldable_key("tug"));
        assert!(foldable_key("automatafl"));
        for k in ["council", "market", "doc", "trade", "descent", ""] {
            assert!(!foldable_key(k), "`{k}` must not offer a fold");
        }
        assert_eq!(game_of_key("tug"), Some(Game::MultiwayTug));
        assert_eq!(game_of_key("automatafl"), Some(Game::Automatafl));
        assert_eq!(game_of_key("dungeon"), None);
    }

    #[test]
    fn the_crown_custom_ids_are_namespaced_and_parse_back() {
        // The ids the buttons mint are exactly what `handle_component` splits on.
        for (id, want) in [
            (format!("{PREFIX}:fold:tug"), vec!["crown", "fold", "tug"]),
            (format!("{PREFIX}:status:7"), vec!["crown", "status", "7"]),
            (
                format!("{PREFIX}:reverify:7"),
                vec!["crown", "reverify", "7"],
            ),
        ] {
            let parts: Vec<&str> = id.split(':').collect();
            assert_eq!(parts, want);
        }
        // Foreign ids (the offering wire, the dungeon ballot) do not collide with `crown:`.
        for id in ["offering:fire:tug:comp:3", "fiction:vote:0:1", "start:menu"] {
            assert!(!id.starts_with("crown:"), "{id}");
        }
    }
}
