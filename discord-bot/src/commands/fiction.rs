//! `/dungeon` — a whole Discord channel plays a shared, AI-narrated dungeon on the
//! **REAL dregg executor**.
//!
//! The play path is [`dungeon_on_dregg`]'s committed universe — "The Warden's Keep" —
//! hosted on [`spween_dregg`]'s real [`WorldCell`]: the same `EmbeddedExecutor`, cell,
//! `CellProgram` and [`TurnReceipt`] the flagship substrate uses, NOT `attested-dm`'s
//! toy `WorldCell`/blake3 ledger. What the party pays for and plays is verifiable
//! substrate, not a LARP hash-chain.
//!
//! A channel opens a session, the bot posts the room (Bedrock/gemma narrates it, the
//! scene describes it) with a row of **buttons for the candidate moves**, and every
//! button press is a **ballot** — one write-once vote per Discord user per round,
//! attributed not to a nickname but to that user's derived **dregg identity**
//! (`cipherclerk::UserCipherclerk::derive(...).public_key_hex()`). When the round closes,
//! the **plurality winner** is applied as ONE real cap-bounded turn
//! ([`WorldCell::apply_choice`]): a legal move lands a real [`TurnReceipt`] (the receipt
//! chain grows); an illegal one — a move the executor's installed `StateConstraint`
//! refuses (a killing blow past the HP floor, a second grab of a `WriteOnce` relic, an
//! over-budget ward, a climb up a one-way stair) — is a real [`WorldError::Refused`]:
//! the crowd decided, the world disposed, nothing commits, no receipt (the anti-ghost
//! tooth). `/dungeon verify` re-verifies the whole receipt chain by REPLAY
//! ([`spween_dregg::verify_by_replay`]) — re-driving a fresh, identically-seeded
//! world-cell through the recorded choices and confirming it reproduces exactly the
//! committed state chain. A forged/reordered record fails.
//!
//! The executor is the SOURCE OF TRUTH: the AI narrates, the world resolves, the chain
//! remembers. A jailbroken narration cannot open a gated stair or mint an unearned
//! relic — only a move the verified executor admits ever changes the world.

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use serenity::all::{
    ButtonStyle, CommandInteraction, CommandOptionType, ComponentInteraction, Context,
    CreateActionRow, CreateButton, CreateCommand, CreateCommandOption, CreateEmbed,
    CreateEmbedFooter, CreateInteractionResponse, CreateInteractionResponseMessage,
};

use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::{deploy_keep, keep_scene};
use spween::{CompareOp, ConditionClause, ConditionExpr, PassageContent, Scene};
use spween_dregg::{
    Playthrough, StepReceipt, VerifyBreak, WorldCell, WorldError, value_to_u64, verify_by_replay,
};

use crate::BotState;
use crate::cipherclerk::UserCipherclerk;

/// The bot-branded teal (matches `embeds::DREGG_COLOR`).
const DUNGEON_COLOR: u32 = 0x7B2CBF;
/// The honest tagline that footers every dungeon surface.
const TAGLINE: &str = "the AI narrates · the world resolves · the chain remembers";
/// The hosted universe's display name.
const KEEP_NAME: &str = "The Warden's Keep";
/// The Keep's objective, stated for the party.
const KEEP_OBJECTIVE: &str = "trade past the gate-warden, claim the crown, descend the collapsing stair, and seize the hoard";

// ─────────────────────────────────────────────────────────────────────────────
// The REAL engine adapter — a session over a dungeon-on-dregg WorldCell.
// ─────────────────────────────────────────────────────────────────────────────

/// The outcome of applying a round's plurality winner as a real turn.
#[derive(Clone, Debug)]
pub enum MoveOutcome {
    /// The move landed as one verified, committed turn — a real [`TurnReceipt`].
    Landed {
        /// The committed turn's receipt (a genuine `turn_hash`, chained pre/post state).
        receipt: TurnReceipt,
        /// Whether this move ended the dungeon (navigated to `END`).
        ended: bool,
    },
    /// The real executor REFUSED the move (an installed `StateConstraint` bit): nothing
    /// committed, no receipt — the anti-ghost tooth. Carries the executor's reason.
    Refused(String),
}

/// **A play session over the REAL substrate.** Owns the live [`WorldCell`] (the committed
/// dungeon-on-dregg Keep), the owned scene (choices/conditions the ballot is built from),
/// the deterministic seed, and the accumulated [`Playthrough`] (genesis + committed steps)
/// that `/dungeon verify` re-verifies by replay.
pub struct RealSession {
    /// The live world-cell — genesis committed, subsequent moves committed on it.
    world: WorldCell,
    /// The owned Keep scene (deterministic; a re-deploy under `seed` reproduces it).
    scene: Scene,
    /// The deterministic deploy seed — `verify` re-deploys a fresh identically-seeded cell.
    seed: u8,
    /// The genesis receipt (intro entry effects + initial passage bind).
    genesis: TurnReceipt,
    /// The committed slot vector right after genesis (the replay verifier reproduces it).
    genesis_state: Vec<u64>,
    /// The committed choice-steps, in order — each a real landed turn.
    steps: Vec<StepReceipt>,
}

impl RealSession {
    /// Open a fresh session hosting the Keep: deploy a real world-cell under `seed`, run
    /// the intro's entry effects as the genesis turn (via the stock [`Driver`], which we
    /// then finish to hold the post-genesis cell), and record the genesis snapshot.
    pub fn open(seed: u8) -> Result<RealSession, WorldError> {
        let scene = keep_scene();
        let world = deploy_keep(seed);
        // Drive genesis with the stock runtime (intro entry effects: hp=50, mana_budget=50),
        // then finish to hold the post-genesis world-cell for direct `apply_choice` play.
        let driver = spween_dregg::Driver::start(world, &scene)?;
        let genesis = driver.genesis().cloned().unwrap_or_default();
        let genesis_state = driver.playthrough().genesis_state;
        let (world, _no_steps) = driver.finish();
        Ok(RealSession {
            world,
            scene,
            seed,
            genesis,
            genesis_state,
            steps: Vec::new(),
        })
    }

    /// The current passage name (the "room"), if the dungeon is still running.
    pub fn current_passage_name(&self) -> Option<String> {
        let idx = self.world.read_passage()?;
        self.scene.passages.get(idx).map(|p| p.name.to_string())
    }

    /// The current room's prose (the scene's authored description of the passage).
    pub fn current_prose(&self) -> String {
        let Some(idx) = self.world.read_passage() else {
            return String::new();
        };
        let Some(passage) = self.scene.passages.get(idx) else {
            return String::new();
        };
        let mut out = String::new();
        for c in &passage.content {
            if let PassageContent::Prose(p) = c {
                if !out.is_empty() {
                    out.push(' ');
                }
                out.push_str(p.text.trim());
            }
        }
        out
    }

    /// Whether the dungeon has ended.
    pub fn is_ended(&self) -> bool {
        self.world.read_passage().is_none()
    }

    /// The number of real verified turns so far (genesis + committed steps).
    pub fn receipts_len(&self) -> usize {
        1 + self.steps.len()
    }

    /// Read a narrative var off the committed cell state.
    pub fn read_var(&self, name: &str) -> u64 {
        self.world.read_var(name)
    }

    /// **Build the ballot for the current room** — the current passage's choices, in the
    /// SAME order the compiler indexed them (so the ballot option's `choice_index` is
    /// exactly the index [`WorldCell::apply_choice`] checks the gate case against). A
    /// choice whose scene condition currently fails is marked `🔒` (a decoration; the
    /// executor is the sole referee — a transition-gated illegal move still surfaces as a
    /// real refusal on close).
    pub fn round_options(&self) -> Vec<VoteOption> {
        let Some(idx) = self.world.read_passage() else {
            return Vec::new();
        };
        let Some(passage) = self.scene.passages.get(idx) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for (choice_index, choice) in passage
            .content
            .iter()
            .filter_map(|c| match c {
                PassageContent::Choice(ch) => Some(ch),
                _ => None,
            })
            .enumerate()
        {
            let available = choice
                .condition
                .as_ref()
                .map(|c| eval_condition(&c.expr, &self.world))
                .unwrap_or(true);
            let label = if available {
                choice.text.to_string()
            } else {
                format!("🔒 {}", choice.text)
            };
            out.push(VoteOption {
                label: truncate(&label, 80),
                choice_index,
            });
        }
        out
    }

    /// **Apply a winning choice as ONE real cap-bounded turn.** The `choice_index` is the
    /// index of the winning move among the current passage's choices. A legal move commits
    /// a real [`TurnReceipt`] (recorded onto the playthrough); an illegal one is a real
    /// [`WorldError::Refused`] — nothing commits, no step recorded (anti-ghost).
    pub fn apply_winner(&mut self, choice_index: usize) -> MoveOutcome {
        let Some(idx) = self.world.read_passage() else {
            return MoveOutcome::Refused("the dungeon has already ended".to_string());
        };
        let passage_name = match self.scene.passages.get(idx) {
            Some(p) => p.name.to_string(),
            None => return MoveOutcome::Refused("no current passage".to_string()),
        };
        let Some(choice) = nth_choice(&self.scene, &passage_name, choice_index) else {
            return MoveOutcome::Refused("that move is not on the current ballot".to_string());
        };
        match self
            .world
            .apply_choice(&passage_name, choice_index, &choice)
        {
            Ok(receipt) => {
                let step = StepReceipt {
                    passage: passage_name,
                    choice_index,
                    receipt: receipt.clone(),
                    state: self.world.snapshot(),
                };
                self.steps.push(step);
                let ended = self.world.read_passage().is_none();
                MoveOutcome::Landed { receipt, ended }
            }
            Err(WorldError::Refused(why)) => MoveOutcome::Refused(why),
            Err(e) => MoveOutcome::Refused(e.to_string()),
        }
    }

    /// The recorded playthrough (genesis + committed steps) — the input to replay-verify.
    pub fn playthrough(&self) -> Playthrough {
        Playthrough {
            genesis: self.genesis.clone(),
            genesis_state: self.genesis_state.clone(),
            steps: self.steps.clone(),
        }
    }

    /// **Re-verify the whole receipt chain by REPLAY.** Re-drives a fresh, identically-
    /// seeded world-cell through the recorded choices and confirms it reproduces exactly
    /// the committed state chain in passage order (a forged/reordered record fails). This
    /// is [`spween_dregg::verify_by_replay`] over the real substrate — not a hash-chain walk.
    pub fn verify(&self) -> Result<(), VerifyBreak> {
        verify_by_replay(deploy_keep(self.seed), &self.scene, &self.playthrough())
    }

    /// A compact one-line projection of the party's committed state (for the embed).
    pub fn state_line(&self) -> String {
        let owner = match self.read_var("relic_owner") {
            1 => "Red Hand",
            2 => "Blue Hand",
            _ => "unclaimed",
        };
        format!(
            "HP {} · depth {} · gold {} · crown {} · will spent {}",
            self.read_var("hp"),
            self.read_var("depth"),
            self.read_var("gold"),
            owner,
            self.read_var("mana_spent"),
        )
    }
}

/// Pull the `n`-th `Choice` out of `passage` in the scene (the same ordering the compiler
/// indexes with `choice_method(passage, n)`). `None` if the passage or index is absent — a
/// non-panicking lookup used when applying a possibly-stale ballot winner.
fn nth_choice(scene: &Scene, passage_name: &str, n: usize) -> Option<spween::Choice> {
    let passage = scene
        .passages
        .iter()
        .find(|p| p.name.as_str() == passage_name)?;
    passage
        .content
        .iter()
        .filter_map(|c| match c {
            PassageContent::Choice(ch) => Some(ch),
            _ => None,
        })
        .nth(n)
        .cloned()
}

/// Evaluate a scene condition against the committed cell state (mirrors the runtime's own
/// evaluation via the public world reads). Used only to decorate a ballot label with `🔒`;
/// the installed `CellProgram` gate is the sole authority over whether the move lands.
fn eval_condition(expr: &ConditionExpr, world: &WorldCell) -> bool {
    match expr {
        ConditionExpr::Atom(clause) => eval_clause(clause, world),
        ConditionExpr::And(a, b) => eval_condition(a, world) && eval_condition(b, world),
        ConditionExpr::Or(a, b) => eval_condition(a, world) || eval_condition(b, world),
    }
}

fn eval_clause(clause: &ConditionClause, world: &WorldCell) -> bool {
    match clause {
        ConditionClause::Has(h) => world.read_membership(&h.category, &h.key),
        ConditionClause::Compare(c) => {
            let lhs = world.read_var(&c.var);
            let rhs = value_to_u64(&c.value);
            match c.op {
                CompareOp::Ge => lhs >= rhs,
                CompareOp::Le => lhs <= rhs,
                CompareOp::Gt => lhs > rhs,
                CompareOp::Lt => lhs < rhs,
                CompareOp::Eq => lhs == rhs,
                CompareOp::Ne => lhs != rhs,
            }
        }
        ConditionClause::Not(inner) => !eval_clause(inner, world),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The round / ballot model — the write-once vote, the tally, the plurality winner.
// (KEPT verbatim from the collective mechanism — the crowd decides, the world disposes.)
// ─────────────────────────────────────────────────────────────────────────────

/// One candidate move on the ballot — its human label and the real scene choice index it
/// resolves to (the index [`WorldCell::apply_choice`] checks the gate case against).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoteOption {
    /// The button label (e.g. `"Press on into the plundered hall"`, `"🔒 Trade blows"`).
    pub label: String,
    /// The scene choice index (within the current passage) this option applies.
    pub choice_index: usize,
}

/// **A voting round** — the candidate moves and the write-once ballots cast against them. A
/// voter is a **derived dregg public key** (hex), never a Discord nickname: a ballot is
/// attributable to a real cryptographic identity.
#[derive(Clone, Debug, Default)]
pub struct Round {
    /// The round number (monotonic per session). A ballot for a stale round is rejected.
    pub round: u64,
    /// The candidate moves, in stable order (the position is the ballot's option id).
    pub options: Vec<VoteOption>,
    /// The ballots cast: voter public-key hex → chosen option position. **Write-once**: a
    /// second vote from the same key is refused (see [`Round::cast`]).
    pub ballots: HashMap<String, usize>,
}

/// The outcome of attempting to cast a ballot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BallotOutcome {
    /// The ballot was recorded (first vote from this voter this round).
    Recorded,
    /// The voter already voted this round — the ballot is refused (write-once).
    AlreadyVoted,
    /// The option index is out of range for this round.
    BadOption,
}

impl Round {
    /// A fresh round with the given number and candidate options.
    pub fn new(round: u64, options: Vec<VoteOption>) -> Round {
        Round {
            round,
            options,
            ballots: HashMap::new(),
        }
    }

    /// **Cast a write-once ballot.** `voter` is the voter's derived dregg public-key hex. The
    /// first vote is [`BallotOutcome::Recorded`]; any later vote from the same key is
    /// [`BallotOutcome::AlreadyVoted`] (the world does not let a voter stuff the box). An
    /// out-of-range option is [`BallotOutcome::BadOption`].
    pub fn cast(&mut self, voter: &str, option: usize) -> BallotOutcome {
        if option >= self.options.len() {
            return BallotOutcome::BadOption;
        }
        if self.ballots.contains_key(voter) {
            return BallotOutcome::AlreadyVoted;
        }
        self.ballots.insert(voter.to_string(), option);
        BallotOutcome::Recorded
    }

    /// The vote count per option position, in option order.
    pub fn tally(&self) -> Vec<usize> {
        let mut counts = vec![0usize; self.options.len()];
        for &idx in self.ballots.values() {
            if idx < counts.len() {
                counts[idx] += 1;
            }
        }
        counts
    }

    /// **The plurality winner's option position** — the option with the most votes, ties
    /// broken **deterministically toward the lowest option index** (documented, reproducible).
    /// `None` only when there are no options at all; a round with options but zero ballots
    /// still resolves to option `0` (the deterministic default the crowd left to the world).
    pub fn winner(&self) -> Option<usize> {
        if self.options.is_empty() {
            return None;
        }
        let counts = self.tally();
        (0..self.options.len()).max_by_key(|&i| (counts[i], std::cmp::Reverse(i)))
    }
}

/// A per-channel play session — the real engine, the world's name, the live round, and how
/// the last narration was produced (never misreported).
pub struct DungeonSession {
    /// The REAL engine session (world-cell + receipt chain).
    pub real: RealSession,
    /// The world's display name.
    pub name: String,
    /// The live voting round.
    pub round: Round,
    /// How the current room narration was produced (bedrock / gemma / scripted).
    pub narrator: NarratorKind,
    /// The narration text posted for the current room — kept so a live vote re-render
    /// preserves the prose (a vote never re-hits the network, so it never misreports it).
    pub last_narration: String,
}

/// How a piece of narration was produced — surfaced honestly in the embed footer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NarratorKind {
    /// A real hosted model (AWS Bedrock) narrated it — a PAID run that spent one $DREGG credit.
    Bedrock,
    /// A real local `gemma2:2b` (ollama) narrated it (the free tier).
    Gemma,
    /// ollama was unreachable; the scene's own scripted description stood in (the free tier).
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

/// The per-channel session store — keyed by Discord channel id. A module-global (behind a
/// `OnceLock<Mutex<…>>`) so it needs no change to `BotState`; every command locks it briefly
/// and never holds the guard across an `.await` (narration happens outside the lock).
fn sessions() -> &'static Mutex<HashMap<u64, DungeonSession>> {
    static SESSIONS: OnceLock<Mutex<HashMap<u64, DungeonSession>>> = OnceLock::new();
    SESSIONS.get_or_init(|| Mutex::new(HashMap::new()))
}

/// The deterministic deploy seed for a channel's session (stable per channel, so a re-open
/// reproduces the same world identity — what the replay verifier leans on).
fn channel_seed(channel: u64) -> u8 {
    ((channel % 251) + 1) as u8
}

// ─────────────────────────────────────────────────────────────────────────────
// Registration + slash routing.
// ─────────────────────────────────────────────────────────────────────────────

/// Register the `/dungeon` command (list / start / close / verify).
pub fn register() -> CreateCommand {
    CreateCommand::new("dungeon")
        .description("Play a shared, AI-narrated dungeon on the REAL dregg executor, as a channel")
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "list",
            "Describe the hosted world and its executor-enforced rules",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "start",
            "Open the Warden's Keep in this channel (a real world-cell)",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "close",
            "Close the round: apply the party's plurality choice as a real turn, post the next round",
        ))
        .add_option(CreateCommandOption::new(
            CommandOptionType::SubCommand,
            "verify",
            "Re-verify this channel's playthrough by replay (the real receipt chain)",
        ))
}

/// Route `/dungeon` subcommands.
pub async fn handle(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let Some(sub) = command.data.options.first() else {
        return;
    };
    match sub.name.as_str() {
        "list" => handle_list(ctx, command).await,
        "start" => handle_start(ctx, command, state).await,
        "close" => handle_close(ctx, command, state).await,
        "verify" => handle_verify(ctx, command).await,
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

// ─── /dungeon list ───────────────────────────────────────────────────────────

async fn handle_list(ctx: &Context, command: &CommandInteraction) {
    let desc = format!(
        "**{KEEP_NAME}** — a dungeon hosted on the REAL dregg executor.\n\n\
         Every move is one cap-bounded turn the verified executor admits; every rule is an \
         executor-enforced `StateConstraint`, not app bookkeeping:\n\
         • **the gate-warden** — a killing blow past the HP floor is refused (`FieldGte`)\n\
         • **the reliquary crown** — the first hand to close on it holds it; a rival re-claim is refused (`WriteOnce`)\n\
         • **the collapsing stair** — descent is one-way; climbing back is refused (`Monotonic`)\n\
         • **the sealing ward** — will is a finite budget; an over-spend is refused (`FieldLteField`)\n\n\
         Open it with `/dungeon start`. Each button is a write-once ballot (one vote per \
         dregg identity); `/dungeon close` applies the party's plurality choice as a real \
         turn; `/dungeon verify` re-verifies the receipt chain by replay."
    );
    let embed = base_embed(&format!("{KEEP_NAME} — the hosted world"))
        .description(desc)
        .footer(footer(NarratorKind::Scripted));
    respond(ctx, command, embed, vec![], true).await;
}

// ─── /dungeon start ──────────────────────────────────────────────────────────

async fn handle_start(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let channel = command.channel_id.get();
    let seed = channel_seed(channel);

    // Deploy the real world-cell FIRST (no lock, no network) — fail-closed if it refuses.
    let real = match RealSession::open(seed) {
        Ok(r) => r,
        Err(e) => {
            let embed = error_embed(
                "The Keep did not deploy",
                &format!("The world-cell deploy failed: {e}"),
            );
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
    };

    // Insert the session + first round inside the lock, snapshot the render data, then
    // narrate OUTSIDE the lock (narration hits the network).
    let (room_name, room_desc, snap) = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        let options = real.round_options();
        let room_name = real
            .current_passage_name()
            .unwrap_or_else(|| "the threshold".to_string());
        let room_desc = real.current_prose();
        let round = Round::new(0, options);
        let sess = DungeonSession {
            real,
            name: KEEP_NAME.to_string(),
            round,
            narrator: NarratorKind::Scripted,
            last_narration: String::new(),
        };
        let snap = render_snapshot(&sess);
        store.insert(channel, sess);
        (room_name, room_desc, snap)
    };

    let (narration, kind) =
        narrate_room_gated(state, command.user.id.get(), &room_name, &room_desc).await;
    if let Ok(mut store) = sessions().lock() {
        if let Some(sess) = store.get_mut(&channel) {
            sess.narrator = kind;
            sess.last_narration = narration.clone();
        }
    }

    let embed = round_embed(&snap, &narration, kind);
    let rows = ballot_rows(&snap.options, snap.round);
    respond(ctx, command, embed, rows, false).await;
}

// ─── /dungeon close — resolve the plurality winner as a REAL turn ─────────────

async fn handle_close(ctx: &Context, command: &CommandInteraction, state: &BotState) {
    let channel = command.channel_id.get();

    enum CloseRender {
        NoSession,
        Empty,
        Resolved {
            resolution: ResolvedRound,
            next_room_name: String,
            next_room_desc: String,
            next_snapshot: Option<RenderSnapshot>,
        },
    }

    let render = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get_mut(&channel) {
            None => CloseRender::NoSession,
            Some(sess) => match sess.round.winner() {
                None => CloseRender::Empty,
                Some(winner_pos) => {
                    let winner = sess.round.options[winner_pos].clone();
                    let tally = sess.round.tally();
                    let votes_for_winner = tally.get(winner_pos).copied().unwrap_or(0);
                    let total_ballots = sess.round.ballots.len();
                    let round_no = sess.round.round;
                    let was_tie = is_tie(&tally, winner_pos);

                    // THE WORLD DISPOSES — apply the crowd's choice as one real cap-bounded turn.
                    let outcome = sess.real.apply_winner(winner.choice_index);
                    let receipts = sess.real.receipts_len();

                    let resolution = ResolvedRound {
                        world_name: sess.name.clone(),
                        round_no,
                        winner_label: winner.label.clone(),
                        votes_for_winner,
                        total_ballots,
                        was_tie,
                        result: describe_outcome(&outcome),
                        ended: sess.real.is_ended(),
                        receipts,
                    };

                    if sess.real.is_ended() {
                        CloseRender::Resolved {
                            resolution,
                            next_room_name: String::new(),
                            next_room_desc: String::new(),
                            next_snapshot: None,
                        }
                    } else {
                        let options = sess.real.round_options();
                        let next = Round::new(round_no + 1, options);
                        sess.round = next;
                        let next_room_name = sess
                            .real
                            .current_passage_name()
                            .unwrap_or_else(|| "the dark".to_string());
                        let next_room_desc = sess.real.current_prose();
                        let snap = render_snapshot(sess);
                        CloseRender::Resolved {
                            resolution,
                            next_room_name,
                            next_room_desc,
                            next_snapshot: Some(snap),
                        }
                    }
                }
            },
        }
    };

    match render {
        CloseRender::NoSession => {
            let embed = warn_embed(
                "No session",
                "This channel has no dungeon open. Start one with `/dungeon start`.",
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        CloseRender::Empty => {
            let embed = warn_embed(
                "No moves",
                "There is nothing to vote on. Try `/dungeon verify` or `/dungeon start` a new run.",
            );
            respond(ctx, command, embed, vec![], true).await;
        }
        CloseRender::Resolved {
            resolution,
            next_room_name,
            next_room_desc,
            next_snapshot,
        } => match next_snapshot {
            Some(snap) => {
                let (narration, kind) = narrate_room_gated(
                    state,
                    command.user.id.get(),
                    &next_room_name,
                    &next_room_desc,
                )
                .await;
                if let Ok(mut store) = sessions().lock() {
                    if let Some(sess) = store.get_mut(&channel) {
                        sess.narrator = kind;
                        sess.last_narration = narration.clone();
                    }
                }
                let embed = resolution_then_round_embed(&resolution, &snap, &narration, kind);
                let rows = ballot_rows(&snap.options, snap.round);
                respond(ctx, command, embed, rows, false).await;
            }
            None => {
                let embed = resolution_final_embed(&resolution);
                respond(ctx, command, embed, vec![], false).await;
            }
        },
    }
}

/// Whether the winning option `pos` shares its vote count with ANY OTHER option — i.e. the
/// deterministic lowest-index tie-break was exercised.
fn is_tie(tally: &[usize], pos: usize) -> bool {
    let top = tally.get(pos).copied().unwrap_or(0);
    tally.iter().enumerate().any(|(j, &c)| j != pos && c == top)
}

/// A plain-language account of a move outcome for the channel.
struct ResultView {
    /// The headline line.
    headline: String,
    /// The engine's own narration (the executor refusal reason on a refusal).
    body: String,
    /// Whether this landed a real receipt.
    landed: bool,
}

fn describe_outcome(outcome: &MoveOutcome) -> ResultView {
    match outcome {
        MoveOutcome::Landed { .. } => ResultView {
            headline: "A verified turn landed on the chain.".to_string(),
            body:
                "The world resolved the party's choice — a real, committed, executor-admitted turn."
                    .to_string(),
            landed: true,
        },
        MoveOutcome::Refused(why) => ResultView {
            headline:
                "Refused — the crowd decided, the world disposed: room unchanged, no receipt."
                    .to_string(),
            body: format!("The executor refused the move: {why}"),
            landed: false,
        },
    }
}

/// The resolved-round facts to render.
struct ResolvedRound {
    world_name: String,
    round_no: u64,
    winner_label: String,
    votes_for_winner: usize,
    total_ballots: usize,
    was_tie: bool,
    result: ResultView,
    ended: bool,
    receipts: usize,
}

// ─── /dungeon verify ─────────────────────────────────────────────────────────

async fn handle_verify(ctx: &Context, command: &CommandInteraction) {
    let channel = command.channel_id.get();
    enum VerifyOutcome {
        NoSession,
        Result {
            verified: bool,
            count: usize,
            name: String,
            break_msg: Option<String>,
        },
    }
    let outcome = {
        let store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get(&channel) {
            None => VerifyOutcome::NoSession,
            Some(sess) => {
                let count = sess.real.receipts_len();
                match sess.real.verify() {
                    Ok(()) => VerifyOutcome::Result {
                        verified: true,
                        count,
                        name: sess.name.clone(),
                        break_msg: None,
                    },
                    Err(b) => VerifyOutcome::Result {
                        verified: false,
                        count,
                        name: sess.name.clone(),
                        break_msg: Some(b.to_string()),
                    },
                }
            }
        }
    };
    let (verified, count, name, break_msg) = match outcome {
        VerifyOutcome::NoSession => {
            let embed = warn_embed(
                "No session",
                "This channel has no dungeon open. Start one with `/dungeon start`.",
            );
            respond(ctx, command, embed, vec![], true).await;
            return;
        }
        VerifyOutcome::Result {
            verified,
            count,
            name,
            break_msg,
        } => (verified, count, name, break_msg),
    };
    let embed = if verified {
        base_embed(&format!("✓ {name} — playthrough re-verifies by replay"))
            .description(format!(
                "**{count} verified turns** re-verify: a fresh, identically-seeded world-cell, re-driven through the recorded choices, reproduces exactly this committed state chain in passage order.\n\nA reordered, mutated, or forged (ineligible) choice would break replay — the executor refuses on re-drive, or the reproduced state diverges."
            ))
            .footer(footer(NarratorKind::Scripted))
    } else {
        error_embed(
            &format!("✗ {name} — replay BREAKS"),
            &format!(
                "The playthrough did not re-verify:\n`{}`",
                break_msg.unwrap_or_default()
            ),
        )
    };
    respond(ctx, command, embed, vec![], false).await;
}

// ─────────────────────────────────────────────────────────────────────────────
// Component route — a button press is a ballot.
// ─────────────────────────────────────────────────────────────────────────────

/// Route a `fiction:` component press (a ballot). custom_id: `fiction:vote:<round>:<optionPos>`.
pub async fn handle_component(ctx: &Context, component: &ComponentInteraction, state: &BotState) {
    let id = component.data.custom_id.clone();
    let parts: Vec<&str> = id.split(':').collect();
    if parts.len() != 4 || parts[1] != "vote" {
        return;
    }
    let round: u64 = parts[2].parse().unwrap_or(u64::MAX);
    let option: usize = match parts[3].parse() {
        Ok(n) => n,
        Err(_) => return,
    };

    let channel = component.channel_id.get();
    let user_id = component.user.id.get();

    // The voter id is the user's DERIVED DREGG IDENTITY — its Ed25519 public key hex — NOT the
    // Discord nickname. Deterministic per (bot_secret, user id, federation).
    let voter =
        UserCipherclerk::derive(&state.config.bot_secret, user_id, state.federation_id_bytes)
            .public_key_hex()
            .to_string();

    enum Reply {
        Ephemeral(String),
        Update {
            snapshot: RenderSnapshot,
            narration: String,
            kind: NarratorKind,
        },
    }

    let reply = {
        let mut store = sessions().lock().unwrap_or_else(|e| e.into_inner());
        match store.get_mut(&channel) {
            None => Reply::Ephemeral(
                "There is no dungeon open in this channel. Start one with `/dungeon start`."
                    .to_string(),
            ),
            Some(sess) => {
                if sess.round.round != round {
                    Reply::Ephemeral(
                        "That round already closed. Vote on the current round's buttons."
                            .to_string(),
                    )
                } else {
                    match sess.round.cast(&voter, option) {
                        BallotOutcome::AlreadyVoted => Reply::Ephemeral(format!(
                            "You already voted this round (as `{}…`). One ballot per identity.",
                            &voter[..voter.len().min(16)]
                        )),
                        BallotOutcome::BadOption => {
                            Reply::Ephemeral("That option is no longer on the ballot.".to_string())
                        }
                        BallotOutcome::Recorded => {
                            let snapshot = render_snapshot(sess);
                            Reply::Update {
                                snapshot,
                                narration: sess.last_narration.clone(),
                                kind: sess.narrator,
                            }
                        }
                    }
                }
            }
        }
    };

    match reply {
        Reply::Ephemeral(text) => {
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
        Reply::Update {
            snapshot,
            narration,
            kind,
        } => {
            let narration = if narration.trim().is_empty() {
                snapshot.room_desc.clone()
            } else {
                narration
            };
            let embed = round_embed(&snapshot, &narration, kind);
            let rows = ballot_rows(&snapshot.options, snapshot.round);
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
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Rendering — embeds + ballot buttons.
// ─────────────────────────────────────────────────────────────────────────────

/// A snapshot of everything needed to render a round embed + its buttons, taken while the
/// lock is held so the network narration can happen afterwards without the lock.
#[derive(Clone)]
pub struct RenderSnapshot {
    world_name: String,
    round: u64,
    room_name: String,
    room_desc: String,
    state_line: String,
    objective: String,
    receipts: usize,
    options: Vec<VoteOption>,
    tally: Vec<usize>,
    ballots: usize,
}

fn render_snapshot(sess: &DungeonSession) -> RenderSnapshot {
    let room_name = sess
        .real
        .current_passage_name()
        .unwrap_or_else(|| "the dark".to_string());
    RenderSnapshot {
        world_name: sess.name.clone(),
        round: sess.round.round,
        room_name,
        room_desc: sess.real.current_prose(),
        state_line: sess.real.state_line(),
        objective: KEEP_OBJECTIVE.to_string(),
        receipts: sess.real.receipts_len(),
        options: sess.round.options.clone(),
        tally: sess.round.tally(),
        ballots: sess.round.ballots.len(),
    }
}

/// The round embed: the room (narrated), state, objective, receipts, and the live ballot.
fn round_embed(snap: &RenderSnapshot, narration: &str, kind: NarratorKind) -> CreateEmbed {
    let mut desc = String::new();
    desc.push_str(&truncate(narration, 1400));
    if narration.trim() != snap.room_desc.trim() && !snap.room_desc.trim().is_empty() {
        desc.push_str("\n\n");
        desc.push_str(&format!("_{}_", truncate(&snap.room_desc, 800)));
    }

    base_embed(&format!("{} — {}", snap.world_name, snap.room_name))
        .description(truncate(&desc, 4000))
        .field("Party", snap.state_line.clone(), false)
        .field("Objective", snap.objective.clone(), false)
        .field("Verified turns", snap.receipts.to_string(), true)
        .field(
            format!("Round {}", snap.round),
            format!("{} ballot(s) cast", snap.ballots),
            true,
        )
        .field(
            "The party's move — vote a button below",
            tally_block(&snap.options, &snap.tally),
            false,
        )
        .footer(footer(kind))
}

/// The combined "round resolved → next round" embed after `/dungeon close`.
fn resolution_then_round_embed(
    res: &ResolvedRound,
    snap: &RenderSnapshot,
    narration: &str,
    kind: NarratorKind,
) -> CreateEmbed {
    let mut embed = round_embed(snap, narration, kind);
    let tie = if res.was_tie {
        " (tie → lowest option index)"
    } else {
        ""
    };
    let outcome = format!(
        "**Round {} closed.** The party chose **{}** with {}/{} ballot(s){}.\n\n{}\n> {}",
        res.round_no,
        res.winner_label,
        res.votes_for_winner,
        res.total_ballots,
        tie,
        res.result.headline,
        truncate(&res.result.body, 600),
    );
    embed = embed.field("Last move", truncate(&outcome, 1000), false);
    embed
}

/// The final embed when the dungeon ended on the closed round.
fn resolution_final_embed(res: &ResolvedRound) -> CreateEmbed {
    let (title, verdict) = if res.ended && res.result.landed {
        (
            "🏆 The Keep is cleared",
            "The objective is met — the crowd carried it out together, one real turn at a time.",
        )
    } else {
        ("The round closed", "")
    };
    let tie = if res.was_tie {
        " (tie → lowest option index)"
    } else {
        ""
    };
    let body = format!(
        "**{}** with {}/{} ballot(s){}.\n\n{}\n> {}\n\n{}\n\n**{} verified turns** on the chain. Run `/dungeon verify` to re-check them by replay.",
        res.winner_label,
        res.votes_for_winner,
        res.total_ballots,
        tie,
        res.result.headline,
        truncate(&res.result.body, 800),
        verdict,
        res.receipts,
    );
    base_embed(&format!("{} — {}", res.world_name, title))
        .description(truncate(&body, 4000))
        .footer(footer(NarratorKind::Scripted))
}

/// A monospace tally block: `Trade blows  ▓▓▓ 3` per option.
fn tally_block(options: &[VoteOption], tally: &[usize]) -> String {
    if options.is_empty() {
        return "—".to_string();
    }
    let mut out = String::new();
    for (i, opt) in options.iter().enumerate() {
        let n = tally.get(i).copied().unwrap_or(0);
        let bar = "▓".repeat(n.min(12));
        out.push_str(&format!(
            "`{:>2}` {} {} {}\n",
            i,
            truncate(&opt.label, 32),
            bar,
            n
        ));
    }
    truncate(&out, 1000)
}

/// The ballot buttons for a round, chunked into Discord action rows of five (max five rows).
fn ballot_rows(options: &[VoteOption], round: u64) -> Vec<CreateActionRow> {
    let mut rows: Vec<CreateActionRow> = Vec::new();
    for (row_idx, chunk) in options.chunks(5).enumerate() {
        if row_idx >= 5 {
            break;
        }
        let mut buttons: Vec<CreateButton> = Vec::new();
        for (i, opt) in chunk.iter().enumerate() {
            let idx = row_idx * 5 + i;
            let style = if opt.label.starts_with('🔒') {
                ButtonStyle::Danger
            } else {
                ButtonStyle::Primary
            };
            buttons.push(
                CreateButton::new(format!("fiction:vote:{round}:{idx}"))
                    .label(truncate(&opt.label, 78))
                    .style(style),
            );
        }
        rows.push(CreateActionRow::Buttons(buttons));
    }
    rows
}

fn base_embed(title: &str) -> CreateEmbed {
    CreateEmbed::new().title(title).color(DUNGEON_COLOR)
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
    CreateEmbedFooter::new(format!("{} · {}", kind.label(), TAGLINE))
}

// ─────────────────────────────────────────────────────────────────────────────
// The narrator — a real hosted Bedrock (paid), local gemma2:2b (free), scripted fallback.
// ─────────────────────────────────────────────────────────────────────────────

/// **The credit gate.** Narrate a room for `discord_user_id`, spending a `$DREGG` run-credit
/// on a real Bedrock narration when the user has one, else falling back to the FREE tier
/// ([`narrate_room`], ollama/scripted). The paid backend is never free-ridden: a paid
/// narration debits exactly one credit AFTER a successful hosted call. The narrator kind is
/// reported honestly.
async fn narrate_room_gated(
    state: &BotState,
    discord_user_id: u64,
    room_name: &str,
    room_desc: &str,
) -> (String, NarratorKind) {
    let discord = discord_user_id.to_string();

    if !state.pay.can_run_paid(&discord) {
        return narrate_room(room_name, room_desc).await;
    }
    let Some(paid) = state.pay.paid.clone() else {
        return narrate_room(room_name, room_desc).await;
    };

    let system = "You are the dungeon master of a shared party dungeon crawl. In two vivid \
                  sentences, set the scene for the party as they arrive. Do NOT use curly braces."
        .to_string();
    let prompt = format!("Room: {room_name}. {room_desc}");

    // The hosted Bedrock client drives its OWN Tokio runtime with `block_on`, which must not run
    // on a bot async worker — do the paid narration on a blocking thread.
    let narration = tokio::task::spawn_blocking(move || paid.narrate(&system, &prompt))
        .await
        .ok()
        .and_then(|r| r.ok())
        .filter(|n| !n.text.trim().is_empty());

    match narration {
        Some(n) => {
            let _ = state.pay.debit_one(&discord);
            (sanitize(&n.text), NarratorKind::Bedrock)
        }
        None => narrate_room(room_name, room_desc).await,
    }
}

/// Narrate a room (the FREE tier). Tries a real local `gemma2:2b` over ollama; if unreachable
/// OR returns nothing usable, falls back to the scene's own scripted description and reports
/// `NarratorKind::Scripted` — the narrator is NEVER misreported.
async fn narrate_room(room_name: &str, room_desc: &str) -> (String, NarratorKind) {
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
        "You are the dungeon master of a shared party dungeon crawl. In two vivid sentences, \
         set the scene for the party as they arrive. Do NOT use curly braces. \
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

/// Drop the two JSON-hostile bytes + control chars but KEEP `{`/`}` (so a would-be `{{` is not
/// laundered). The executor is what actually refuses an injecting move; here we only tidy display.
fn sanitize(s: &str) -> String {
    s.chars()
        .filter(|c| *c != '"' && *c != '\\' && !c.is_control() || *c == '\n')
        .collect::<String>()
        .trim()
        .to_string()
}

// ─────────────────────────────────────────────────────────────────────────────
// Small helpers.
// ─────────────────────────────────────────────────────────────────────────────

/// Truncate `s` to at most `max` characters (char-safe), appending `…` when cut.
fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max.saturating_sub(1)).collect();
    out.push('…');
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests — the round/ballot logic, the REAL-engine seam (a legal winner lands a real
// receipt; an illegal winner is a real executor refusal), the deterministic voter-id.
// No live Discord required.
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dungeon_on_dregg::{KP_PRESS_ON, KP_TRADE_BLOWS};

    fn opt(label: &str, choice_index: usize) -> VoteOption {
        VoteOption {
            label: label.to_string(),
            choice_index,
        }
    }

    // ── (a) round / ballot logic ─────────────────────────────────────────────

    #[test]
    fn a_ballot_is_write_once_per_voter() {
        let mut round = Round::new(0, vec![opt("go north", 0), opt("look", 1)]);
        assert_eq!(round.cast("pubkey_alice", 0), BallotOutcome::Recorded);
        assert_eq!(round.cast("pubkey_alice", 1), BallotOutcome::AlreadyVoted);
        assert_eq!(round.tally(), vec![1, 0]);
        assert_eq!(round.cast("pubkey_bob", 1), BallotOutcome::Recorded);
        assert_eq!(round.tally(), vec![1, 1]);
    }

    #[test]
    fn a_bad_option_index_is_refused() {
        let mut round = Round::new(0, vec![opt("look", 0)]);
        assert_eq!(round.cast("pk", 9), BallotOutcome::BadOption);
        assert!(round.ballots.is_empty());
    }

    #[test]
    fn plurality_winner_is_the_most_voted() {
        let mut round = Round::new(0, vec![opt("north", 0), opt("south", 1), opt("look", 2)]);
        round.cast("a", 1);
        round.cast("b", 1);
        round.cast("c", 0);
        assert_eq!(round.winner(), Some(1));
    }

    #[test]
    fn ties_break_toward_the_lowest_option_index() {
        let mut round = Round::new(0, vec![opt("north", 0), opt("south", 1)]);
        round.cast("a", 0);
        round.cast("b", 1);
        assert_eq!(round.winner(), Some(0));
        assert!(is_tie(&round.tally(), 0));
    }

    #[test]
    fn an_empty_round_defaults_to_option_zero() {
        let round = Round::new(0, vec![opt("look", 0)]);
        assert_eq!(round.winner(), Some(0));
    }

    // ── (b) the REAL-engine seam ─────────────────────────────────────────────
    // These supersede the two previously-#[ignore]d attested-dm `sunken_vault` tests:
    // now they drive the REAL dungeon-on-dregg WorldCell (a landed move is a real
    // TurnReceipt; an illegal move is a real executor refusal; verify_by_replay holds).

    /// A voted LEGAL move lands a REAL receipt — the ballot winner is applied as one
    /// cap-bounded turn on the real executor, the receipt count grows, and the whole
    /// playthrough re-verifies by replay against a fresh identically-seeded world-cell.
    #[test]
    fn a_voted_legal_move_lands_a_real_receipt() {
        let mut sess = RealSession::open(7).expect("the Keep opens on a real world-cell");
        assert_eq!(sess.current_passage_name().as_deref(), Some("gatehall"));
        assert_eq!(sess.receipts_len(), 1, "genesis is the first verified turn");

        // "Press on into the plundered hall" — an ungated, legal move (choice KP_PRESS_ON).
        let opts = sess.round_options();
        assert!(
            opts.iter().any(|o| o.choice_index == KP_PRESS_ON),
            "the ballot offers the ungated press-on move"
        );
        match sess.apply_winner(KP_PRESS_ON) {
            MoveOutcome::Landed { receipt, ended } => {
                assert!(!ended, "pressing on does not end the Keep");
                assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
            }
            other => panic!("a legal move must land a real receipt, got {other:?}"),
        }
        assert_eq!(sess.receipts_len(), 2, "a real verified turn landed");
        assert_eq!(
            sess.current_passage_name().as_deref(),
            Some("hall"),
            "the world advanced to the plundered hall"
        );

        // The real receipt chain re-verifies by replay.
        sess.verify()
            .expect("the honest playthrough re-verifies via verify_by_replay");
    }

    /// A voted ILLEGAL move is a REAL executor refusal — world unchanged, no receipt
    /// (the anti-ghost tooth). Two survivable blows land; the killing blow past the HP
    /// floor (`FieldGte`) is refused, and the honest chain still re-verifies.
    #[test]
    fn a_voted_illegal_move_is_a_real_executor_refusal_no_receipt() {
        let mut sess = RealSession::open(8).expect("the Keep opens");

        // Two survivable trade-blows (hp 50 → 30 → 10), each a real committed turn.
        for _ in 0..2 {
            match sess.apply_winner(KP_TRADE_BLOWS) {
                MoveOutcome::Landed { receipt, ended } => {
                    assert!(!ended);
                    assert_ne!(receipt.turn_hash, [0u8; 32]);
                }
                other => panic!("a survivable blow must land, got {other:?}"),
            }
        }
        assert_eq!(sess.read_var("hp"), 10, "two blows dropped hp to 10");
        let receipts_before = sess.receipts_len();

        // At hp 10 the gate-warden choice is now shown locked (its `{ hp >= 21 }` fails).
        let opts = sess.round_options();
        let blow = opts
            .iter()
            .find(|o| o.choice_index == KP_TRADE_BLOWS)
            .expect("the trade-blows move is still on the ballot");
        assert!(
            blow.label.starts_with('🔒'),
            "the killing blow is decorated locked (condition eval), got {:?}",
            blow.label
        );

        // The crowd votes it anyway — the REAL executor refuses (FieldGte on the post-state).
        match sess.apply_winner(KP_TRADE_BLOWS) {
            MoveOutcome::Refused(_) => {}
            other => panic!("a killing blow must be a real executor refusal, got {other:?}"),
        }
        // Anti-ghost: nothing committed.
        assert_eq!(
            sess.receipts_len(),
            receipts_before,
            "no receipt landed for the refused choice"
        );
        assert_eq!(sess.read_var("hp"), 10, "hp unchanged after the refusal");
        assert_eq!(
            sess.current_passage_name().as_deref(),
            Some("gatehall"),
            "still in the gatehall — the world did not move"
        );

        // The honest chain (genesis + two blows) still re-verifies by replay.
        sess.verify()
            .expect("the honest prefix re-verifies after the refusal");
    }

    /// The recorded playthrough re-verifies through a full legal sequence, and a forged
    /// (ineligible) choice fails replay — the real receipt-chain tooth end to end.
    #[test]
    fn the_playthrough_reverifies_and_a_forged_choice_fails() {
        let mut sess = RealSession::open(9).expect("the Keep opens");
        // A legal opening: press on into the hall, claim the crown for the Red Hand.
        assert!(matches!(
            sess.apply_winner(KP_PRESS_ON),
            MoveOutcome::Landed { .. }
        ));
        // hall: claim red (choice 0).
        assert!(matches!(sess.apply_winner(0), MoveOutcome::Landed { .. }));
        sess.verify().expect("the legal playthrough re-verifies");

        // Forge the recorded record: swap the first step's choice for a different one and
        // confirm replay rejects it (state divergence or an executor refusal on re-drive).
        let mut play = sess.playthrough();
        if let Some(first) = play.steps.first_mut() {
            // gatehall had choices 0 (trade-blows) and 1 (press-on); forge 1 → 0.
            first.choice_index = 0;
        }
        let out = verify_by_replay(deploy_keep(9), &sess.scene, &play);
        assert!(
            out.is_err(),
            "a forged choice must fail replay, got {out:?}"
        );
    }

    // ── (c) the voter id IS the cipherclerk-derived public key (deterministic) ──

    #[test]
    fn the_voter_id_equals_the_derived_public_key_deterministically() {
        let bot_secret = [7u8; 32];
        let fed = [9u8; 32];
        let discord_user_id: u64 = 123456789012345678;
        let a = UserCipherclerk::derive(&bot_secret, discord_user_id, fed);
        let b = UserCipherclerk::derive(&bot_secret, discord_user_id, fed);
        assert_eq!(a.public_key_hex(), b.public_key_hex());
        assert_eq!(a.public_key_hex().len(), 64);
        let c = UserCipherclerk::derive(&bot_secret, discord_user_id + 1, fed);
        assert_ne!(a.public_key_hex(), c.public_key_hex());
    }

    #[test]
    fn round_options_offer_the_start_room_moves() {
        let sess = RealSession::open(3).expect("open");
        let options = sess.round_options();
        assert!(
            options.len() >= 2,
            "the gatehall offers more than one candidate move"
        );
        // The ungated press-on move is present and NOT locked.
        let press = options
            .iter()
            .find(|o| o.choice_index == KP_PRESS_ON)
            .expect("press-on present");
        assert!(
            !press.label.starts_with('🔒'),
            "an ungated move is not locked"
        );
    }
}
