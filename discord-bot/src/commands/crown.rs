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

use std::collections::{BTreeMap, HashMap};
use std::sync::OnceLock;
use std::sync::mpsc::{SyncSender, sync_channel};

use serenity::all::{
    ButtonStyle, ChannelId, CommandDataOptionValue, CommandInteraction, CommandOptionType,
    ComponentInteraction, Context, CreateActionRow, CreateAttachment, CreateButton, CreateCommand,
    CreateCommandOption, CreateEmbed, CreateEmbedFooter, CreateInteractionResponse,
    CreateInteractionResponseMessage, CreateMessage,
};

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{RecursionVk, SEG_ANCHOR_WIDTH};

use dregg_automatafl::AutomataflOffering;
use dreggnet_game_board::{
    AnchorProvenance, Game, GameBoard, MatchProof, ProofAnchor, UniverseId, match_anchor,
};
use dreggnet_prove_service::{
    AutomataflMatch, JobId, JobStatus, MatchProveService, MultiRoundTurn, PlayedMatch,
    match_prove_service,
};

use crate::BotState;
use crate::commands::ack;
use crate::commands::offering::{self, identity_of, truncate};
use webauth_core::identity_resolve::RootResolver;

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

/// The OFFERING KEY a board [`Game`] is played through — the inverse of [`game_of_key`], and the
/// only thing a player-facing "go win one" pointer may be built from.
///
/// ⚑ `Game::slug()` is NOT that key. It is the board's own universe slug (`multiway-tug`), and the
/// crown's own copy used it as one — `format!("/play {}", game.slug())` produced
/// `/play multiway-tug`, which is wrong twice over: `/play` needs `open offering:` since
/// `24e47322b`, and `multiway-tug` is not a `/play` choice at all (the key is `tug`).
fn offering_key_of(game: Game) -> &'static str {
    match game {
        Game::MultiwayTug => "tug",
        Game::Automatafl => "automatafl",
    }
}

/// The game's **operator-configured board anchor** — the submission-independent trust root
/// (fixed VK + committed genesis + canonical WIN root), read from an environment variable no
/// player can write, so the board checks every player's proof against a genesis / win it did NOT
/// choose.
///
/// ⚑ MEASURED 2026-07-30. This function used to be `fn canonical_anchor(_game) -> None` — a seam
/// that was never filled — so every deployment fell through to `match_anchor(&proof)`: the board's
/// trust root came from the FIRST fold's own wire and froze there, while the public crown post
/// said *"You do not have to trust the winner."* You did. They chose the anchor.
///
/// `Ok(None)` ⇒ nothing configured, so the board still bootstraps from the first honest fold —
/// and the provenance now rides on every card it prints. `Err` ⇒ the variable is SET and
/// malformed, which is REFUSED rather than downgraded to the bootstrap the operator was
/// configuring their way out of.
///
/// `dreggnet-web`'s `/crown` board calls the SAME function on the SAME variable: the two boards
/// must agree about what they are pinned to, or a cross-surface fold can never rank on both.
fn operator_anchor(game: Game) -> Result<Option<ProofAnchor>, String> {
    dreggnet_game_board::operator_anchor(game)
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
    /// ⚑ **WHERE THE ANCHOR CAME FROM** — the one fact that decides whether this card may say
    /// "you do not have to trust the winner". Carried per fold rather than looked up at render
    /// time, because it is a fact about the pin that happened.
    anchor_provenance: AnchorProvenance,
}

/// One tracked fold: which game, whose, where, and how far along.
struct FoldRecord {
    game: Game,
    /// The Discord channel the match was played in.
    channel: u64,
    /// The submitting player — their derived dregg identity hex (never a nickname).
    player: String,
    /// The background proving job — `None` for a fold RESTORED from durable storage at boot,
    /// which is already ranked and has no in-flight prover work. A pending fold is genuinely
    /// process-local (the prover pool is), so a restored record is never pending.
    job: Option<JobId>,
    /// `Some` once the proof was submitted to (and accepted by) the board.
    ranked: Option<Ranked>,
}

// ─────────────────────────────────────────────────────────────────────────────
// 👑 DURABILITY — why the crown, of everything in this bot, MUST survive a restart.
//
// A crown post is not a session. It is a PUBLIC message in a channel, carrying a
// `.dreggproof` attachment and a button labelled "Re-verify (anyone, O(1))" whose whole
// pitch is *you do not have to trust this bot* — and, ONLY when an operator pinned the
// board's anchor, *you do not have to trust the winner* either. Which of the two the card
// is allowed to say is decided by `Ranked::anchor_provenance`, in one place, in
// `ranked_post`.
// The board that button re-verifies against was an in-memory `GameBoard`, so after any
// restart `reverify_fold` answered `Err("no such fold")` and the post rendered
// "✗ Re-verify refused." A public artifact whose verification affordance stops working is
// worse than one that never offered it: it reads as the claim having been withdrawn.
//
// What is persisted is the proof ENVELOPE plus the board CONFIG it was accepted under (the
// pinned VK + genesis + WIN anchor). NOT the board state, and emphatically not the moves.
// On boot each row is RE-SUBMITTED through `GameBoard::submit_bytes` — the identical O(1)
// light-client accept path a live submission takes — so a restored entry is one this
// process verified itself, this run. A tampered proof, a lied turn count or a swapped
// anchor is REFUSED at exactly the same tooth and simply does not come back.
// ─────────────────────────────────────────────────────────────────────────────

/// One RANKED fold as it is persisted — everything needed to put the entry back on the board
/// and nothing else. `commands::crown` owns this shape; `crate::crown_store` supplies the
/// sqlite impl (the same split `descent`/`DescentBoardStore` uses).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredCrownFold {
    /// The fold token — the id every `crown:status:` / `crown:reverify:` button carries. It is
    /// restored EXACTLY, so a button minted before the restart still addresses this fold.
    pub token: u64,
    /// The game's slug (`tug` / `automatafl`).
    pub game: String,
    /// The Discord channel the match was played in.
    pub channel: u64,
    /// The submitting player's derived dregg identity hex.
    pub player: String,
    /// The attested turn count claimed at submit (re-checked against the proof on restore).
    pub turns: usize,
    /// The pinned anchor's root-circuit VK fingerprint.
    pub vk: [u8; 32],
    /// The pinned anchor's genesis state anchor, as canonical BabyBear limbs.
    pub genesis_root: [u32; SEG_ANCHOR_WIDTH],
    /// The pinned anchor's WIN state anchor, as canonical BabyBear limbs.
    pub win_root: [u32; SEG_ANCHOR_WIDTH],
    /// The succinct whole-history proof envelope — the same bytes the crown post attached.
    pub proof: Vec<u8>,
}

impl StoredCrownFold {
    /// Rebuild the pinned [`ProofAnchor`] this fold was accepted against.
    fn anchor(&self) -> ProofAnchor {
        // `BabyBear::new` reduces, so a hand-edited row cannot smuggle a non-canonical limb
        // past the anchor comparison. (It would still fail the light client; this just keeps
        // the stored representation from being the place a malleability question arises.)
        ProofAnchor::new(
            RecursionVk(self.vk),
            self.genesis_root.map(BabyBear::new),
            self.win_root.map(BabyBear::new),
        )
    }
}

/// **The crown's durable seam.** Sync over `&self` (interior mutability), matching
/// `DescentBoardStore` / `GalleryStore`: the crown board lives on a dedicated non-tokio
/// `std::thread`, so an async DB is bridged inside the impl, not here.
pub trait CrownStore {
    /// Persist a ranked fold. Idempotent by `token`.
    fn persist_fold(&self, fold: &StoredCrownFold) -> Result<(), String>;
    /// Every persisted fold, oldest token first (the anchor-pinning order).
    fn list_folds(&self) -> Result<Vec<StoredCrownFold>, String>;
}

/// The durable crown store, installed once by the main loop at boot ([`install_store`]).
static CROWN_STORE: OnceLock<Box<dyn CrownStore + Send + Sync>> = OnceLock::new();

/// **Main-loop entry point.** Install the durable crown store and force the board thread to
/// spawn NOW, which re-submits every persisted fold through the O(1) accept path. First install
/// wins; call once at boot BEFORE any `/crown` press is served.
pub fn install_store(store: Box<dyn CrownStore + Send + Sync>) {
    let _ = CROWN_STORE.set(store);
    let _ = crown();
}

/// The slug→[`Game`] map used when reloading a persisted row.
fn game_of_slug(slug: &str) -> Option<Game> {
    [Game::MultiwayTug, Game::Automatafl]
        .into_iter()
        .find(|g| g.slug() == slug)
}

/// **Boot restore** — put every persisted fold back on a fresh board by RE-SUBMITTING its proof.
///
/// Each row re-opens its game's board against the anchor it was ranked under (the first row of a
/// game pins it, exactly as the first live fold does) and then goes through
/// `GameBoard::submit_bytes`, which runs the whole-history light client, binds the genesis and
/// WIN roots, and binds the claimed turn count. So this is a re-VERIFICATION, not a restoration
/// of trust: a row that does not survive that gate is dropped with a warning and its button
/// keeps saying refused — which is the honest answer for a proof that no longer verifies.
fn restore_folds(core: &mut CrownCore) {
    let Some(store) = CROWN_STORE.get() else {
        return;
    };
    let rows = match store.list_folds() {
        Ok(rows) => rows,
        Err(e) => {
            tracing::warn!("the crown store could not be read ({e}) — no folds restored");
            return;
        }
    };
    restore_rows(
        &mut core.board,
        &mut core.anchors,
        &mut core.folds,
        &mut core.next_token,
        rows,
    );
}

/// The boot-restore loop over already-listed rows. Split out of [`restore_folds`] so the two
/// restart rules it enforces — the token ALLOCATION and the probe-before-pin — are drivable
/// without standing up the background proving pool (`CrownCore::service`) or the process-global
/// `CROWN_STORE`.
fn restore_rows(
    board: &mut GameBoard,
    anchors: &mut BTreeMap<Game, (ProofAnchor, AnchorProvenance)>,
    folds: &mut HashMap<u64, FoldRecord>,
    next_token: &mut u64,
    rows: Vec<StoredCrownFold>,
) {
    let (mut restored, mut refused) = (0usize, 0usize);
    for row in rows {
        // ⚑ RESERVE THE TOKEN FIRST, verified or not. `next_token` used to advance only in the
        // `Ok` arm below, so a row that did NOT re-verify left the counter under a token already
        // on disk. The next live fold then minted that token, `INSERT OR IGNORE` dropped its row,
        // and the crown vanished at the next restart with nobody told. A token is an ALLOCATION,
        // not a reward: once a row on disk owns one, it is spent.
        *next_token = (*next_token).max(row.token.saturating_add(1));

        let Some(game) = game_of_slug(&row.game) else {
            tracing::warn!("persisted crown fold #{} names no known game", row.token);
            refused += 1;
            continue;
        };

        // ⚑ PIN THE ANCHOR ONLY FROM A ROW THAT SURVIVES IT. `ensure_open` is deliberately
        // write-once, so whatever pins a game's board is that game's trust root for the life of
        // the process. Pinning from `row.anchor()` before anything checked the row let a single
        // corrupt/hand-edited first row freeze the board on attacker-chosen genesis/WIN roots and
        // refuse every honest crown behind it. Probe the candidate on a THROWAWAY board first —
        // one O(1) light-client run, and only for the row that would do the pinning.
        if !anchors.contains_key(&game) {
            // ⚑ AN OPERATOR ANCHOR OUTRANKS THE PERSISTED ONE, and a restart is exactly when a
            // newly-configured one first takes effect. A malformed spec REFUSES the restore of
            // this row rather than falling back to `row.anchor()` — silently reinstating the
            // submitter-pinned board an operator was configuring their way out of is the whole
            // failure this arm exists to prevent.
            let (candidate, provenance) = match operator_anchor(game) {
                Err(e) => {
                    tracing::warn!(
                        "persisted crown fold #{} was NOT restored: {e}. The board stays \
                         unpinned rather than falling back to the fold's own anchor.",
                        row.token,
                    );
                    refused += 1;
                    continue;
                }
                Ok(Some(a)) => (a, AnchorProvenance::OperatorConfigured),
                Ok(None) => (row.anchor(), AnchorProvenance::BootstrappedFromSubmission),
            };
            let mut probe = GameBoard::new();
            probe.ensure_open(game, candidate.clone());
            if let Err(e) = probe.submit_bytes(game, &row.player, row.proof.clone(), row.turns) {
                tracing::warn!(
                    "persisted crown fold #{} did NOT verify against the anchor it would pin the \
                     {} board to ({e}) — it does not pin the board",
                    row.token,
                    game.slug(),
                );
                refused += 1;
                continue;
            }
            if provenance == AnchorProvenance::BootstrappedFromSubmission {
                tracing::warn!(
                    game = game.slug(),
                    env = %dreggnet_game_board::env_var_name(game),
                    "the crown board came up pinned to a PERSISTED SUBMISSION's own anchor — it \
                     will rank self-reported claims until the named variable is set"
                );
            }
            anchors.insert(game, (candidate, provenance));
        }
        let (anchor, provenance) = anchors
            .get(&game)
            .expect("the anchor was just pinned or already present")
            .clone();
        let universe = board.ensure_open(game, anchor);
        // Bound so the board's mutable borrow ends before the fold table is written.
        let submitted = board.submit_bytes(game, &row.player, row.proof.clone(), row.turns);
        match submitted {
            Ok(accepted) => {
                folds.insert(
                    row.token,
                    FoldRecord {
                        game,
                        channel: row.channel,
                        player: row.player,
                        job: None,
                        ranked: Some(Ranked {
                            universe,
                            completion_id: accepted.completion_id,
                            turns: accepted.turns,
                            rank: accepted.rank,
                            proof_len: row.proof.len(),
                            vk8: hex::encode(&row.vk[..4]),
                            anchor_provenance: provenance,
                        }),
                    },
                );
                restored += 1;
            }
            Err(e) => {
                tracing::warn!(
                    "persisted crown fold #{} did NOT re-verify and was not restored: {e}",
                    row.token,
                );
                refused += 1;
            }
        }
    }
    if restored > 0 || refused > 0 {
        tracing::info!(
            "crown board restored {restored} ranked fold(s) by re-running the O(1) light \
             client; {refused} refused",
        );
    }
}

/// Persist a freshly ranked fold, if a durable store is installed. Called on the board thread
/// immediately after the board accepted the proof.
fn persist_fold(token: u64, rec: &FoldRecord, proof: &MatchProof) {
    let Some(store) = CROWN_STORE.get() else {
        return;
    };
    let fold = StoredCrownFold {
        token,
        game: rec.game.slug().to_string(),
        channel: rec.channel,
        player: rec.player.clone(),
        turns: proof.turns(),
        vk: proof.vk.0,
        genesis_root: proof.attested.genesis_root.map(|f| f.0),
        win_root: proof.attested.final_root.map(|f| f.0),
        proof: proof.proof_bytes.clone(),
    };
    if let Err(e) = store.persist_fold(&fold) {
        // A crown that ranked but did not persist is a crown whose public Re-verify button dies
        // at the next restart. Say so loudly; the fold itself is unaffected and still ranked.
        tracing::warn!(
            "crown fold #{token} RANKED but did not persist ({e}) — its public Re-verify \
             button will not survive a restart",
        );
    }
}

/// The owner thread's state: the REAL background prover, the proof-carrying board, the folds.
struct CrownCore {
    service: MatchProveService,
    board: GameBoard,
    /// The per-game board trust anchor, pinned ONCE and never re-minted from a submitted proof,
    /// PLUS where it came from. It is board CONFIG (VK + genesis + WIN roots): operator
    /// configuration when one is set ([`operator_anchor`]), otherwise bootstrapped ONCE from the
    /// first honest fold and frozen. Every later submission is checked against this pinned anchor,
    /// so no LATER submitter can define or replace it — but on the bootstrap arm the FIRST one
    /// already did, which is exactly what [`AnchorProvenance`] carries out to the cards.
    anchors: BTreeMap<Game, (ProofAnchor, AnchorProvenance)>,
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
                    anchors: BTreeMap::new(),
                    folds: HashMap::new(),
                    next_token: 1,
                };
                // Put every persisted crown back on the board FIRST, by re-running the O(1)
                // light client over its stored envelope — so a public crown post's Re-verify
                // button answers before this thread serves its first press.
                restore_folds(&mut core);
                while let Ok(job) = rx.recv() {
                    // Structural net: a panicking job is contained per-job by `run`, and this
                    // guard guarantees no job can unwind out of the loop and kill the thread
                    // (which would brick the crown board for every later caller).
                    let _ =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| job(&mut core)));
                }
            })
            .expect("spawn the crown board thread");
        Crown { jobs }
    })
}

/// Why a crown-board job did not return a value. Both cases used to abort the caller with a
/// panic; now a panicking job is contained (the board thread survives) and the fault is returned
/// to the ONE caller, which degrades gracefully.
#[derive(Debug)]
enum StoreError {
    /// The board thread's channel is closed — it never spawned, or has gone away unrecoverably.
    ThreadGone,
    /// This job panicked; the panic was contained on the board thread, which survives.
    JobPanicked,
}

/// Run `f` on the crown's owner thread and hand back its result. A panic inside `f` is caught on
/// the board thread and returned to THIS caller as [`StoreError::JobPanicked`]; the thread lives
/// on to serve the next job. The happy path is unchanged.
fn run<R: Send + 'static>(
    f: impl FnOnce(&mut CrownCore) -> R + Send + 'static,
) -> Result<R, StoreError> {
    let (tx, rx) = sync_channel::<std::thread::Result<R>>(1);
    crown()
        .jobs
        .send(Box::new(move |core| {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(core)));
            let _ = tx.send(result);
        }))
        .map_err(|_| StoreError::ThreadGone)?;
    match rx.recv() {
        Ok(Ok(value)) => Ok(value),
        Ok(Err(_panic)) => Err(StoreError::JobPanicked),
        Err(_) => Err(StoreError::ThreadGone),
    }
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
    // A store fault degrades to `QueueFull` — the honest "the play already happened, try the fold
    // again shortly" refusal, never a panic.
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
                        job: Some(job),
                        ranked: None,
                    },
                );
                Enqueued::Token(token)
            }
        }
    })
    .unwrap_or(Enqueued::QueueFull)
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
        // A record with no job is a RESTORED fold that somehow lost its ranked facts — it
        // cannot be polled (the prover pool is process-local and never saw it). Say so rather
        // than asking the pool about a job id that does not exist.
        let Some(job) = job else {
            return Poll::Failed(
                "this fold was restored from durable storage and carries no live proving job"
                    .to_string(),
            );
        };
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
                // Pin the board's trust anchor ONCE per game and treat it as IMMUTABLE board
                // CONFIG. `ensure_open` pins it once and ignores every later anchor, so no LATER
                // submitter can capture or replace it — but that has never been the whole story,
                // and ⚑ MEASURED 2026-07-30 this comment used to claim it was ("it is never
                // minted from THIS submitted proof"). Absent an operator anchor the FIRST fold's
                // own `match_anchor(&proof)` becomes the board's genesis and WIN roots and freezes
                // there, so the genesis+win checks self-compare for that fold and every later one
                // is measured against a definition of winning a player supplied. The honest split:
                // [`operator_anchor`] when configured (`AnchorProvenance::OperatorConfigured`),
                // else the bootstrap (`BootstrappedFromSubmission`) — which rides on `Ranked` out
                // to the public card, which then may not say "you do not have to trust the winner".
                let pinned = match core.anchors.get(&game) {
                    Some(p) => p.clone(),
                    None => {
                        // A MALFORMED operator spec REFUSES the rank. Downgrading here would hand
                        // the trust root to this very submitter, which is the thing the operator
                        // was configuring their way out of.
                        let picked = match operator_anchor(game) {
                            Err(e) => return Poll::BoardRefused(e),
                            Ok(Some(a)) => (a, AnchorProvenance::OperatorConfigured),
                            Ok(None) => {
                                tracing::warn!(
                                    game = game.slug(),
                                    env = %dreggnet_game_board::env_var_name(game),
                                    "the crown board is pinning its trust root to THIS submitted \
                                     fold's own anchor and freezing there — it will rank \
                                     self-reported claims until the named variable is set"
                                );
                                (
                                    match_anchor(&proof),
                                    AnchorProvenance::BootstrappedFromSubmission,
                                )
                            }
                        };
                        core.anchors.insert(game, picked.clone());
                        picked
                    }
                };
                let (anchor, provenance) = pinned;
                let universe = core.board.ensure_open(game, anchor);
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
                            anchor_provenance: provenance,
                        };
                        if let Some(rec) = core.folds.get_mut(&token) {
                            rec.ranked = Some(facts.clone());
                        }
                        // DURABLE BEFORE PUBLIC. The very next thing that happens is a public
                        // crown post carrying a Re-verify button; persist the envelope + anchor
                        // here so that button is answerable tomorrow, not just this afternoon.
                        if let Some(rec) = core.folds.get(&token) {
                            persist_fold(token, rec, &proof);
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
    .unwrap_or_else(|_| Poll::Failed("the crown board thread is unavailable".to_string()))
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
            return Err("this fold is not ranked yet; poll its proving status first".to_string());
        };
        core.board
            .registry()
            .reverify_entry(facts.universe, &facts.completion_id)
            .map(|turns| (rec.game, turns, facts))
            .map_err(|why| format!("the light client REFUSED the stored proof: {why}"))
    })
    .unwrap_or_else(|_| Err("the crown board thread is unavailable".to_string()))
}

/// The board read for `/crown board`: per game, the ranked entry lines + the
/// stores-no-moves assertion (asserted alongside non-emptiness, per the API's own note).
///
/// Each fold pins the board to its OWN match anchor (the hand root / genesis differ per
/// match), so ranked entries live across universes — one `open` per rank, and
/// `GameBoard::leaderboard` would show only the LAST-opened universe. The board read here
/// walks the fold records' pinned universes (deduped: publish is content-addressed, so
/// same-anchor folds share one) and merges their entries, ranked by attested turns.
fn board_lines(game: Game) -> (Vec<String>, bool) {
    run(move |core| {
        let mut universes: Vec<UniverseId> = core
            .folds
            .values()
            .filter(|r| r.game == game)
            .filter_map(|r| r.ranked.as_ref().map(|f| f.universe))
            .collect();
        universes.sort_unstable();
        universes.dedup();
        let mut no_moves = true;
        let mut entries: Vec<(usize, String, bool, bool)> = Vec::new();
        // DISPLAY/RANK cross-platform resolution: the board stores the FULL custodial pubkey hex
        // `identity_of` submits under, so resolve it to the human's stable ACCOUNT ID before
        // grouping — a Discord-you and a Telegram-you bound to the same root rank under ONE human.
        // Attribution is untouched (the proof is signed by the custodial key); an unlinked entry
        // resolves to itself, so the board is unchanged for it. The snapshot is loaded ONCE for the
        // whole render (the previous `resolve_display_root` re-scanned the shared TSV PER ROW).
        let resolver = RootResolver::load();
        for u in universes {
            for e in core.board.registry().leaderboard(u) {
                no_moves &= e.is_proof_backed() && !e.has_moves() && e.playthrough().is_none();
                entries.push((
                    e.turns,
                    resolver.resolve(&e.player),
                    e.is_proof_backed(),
                    e.has_moves(),
                ));
            }
        }
        entries.sort();
        // MERGE, don't just relabel. Resolving and then sorting still left one ROW PER CUSTODIAL
        // KEY — two rows for one human, which is exactly the thing the resolution was supposed to
        // fix. Group by the resolved human and keep their BEST (fewest-turns) fold; `entries` is
        // already turns-ordered, so the first sighting of a human IS their best.
        let mut seen: Vec<&String> = Vec::new();
        let mut per_human: Vec<&(usize, String, bool, bool)> = Vec::new();
        for e in &entries {
            if seen.iter().any(|h| *h == &e.1) {
                continue;
            }
            seen.push(&e.1);
            per_human.push(e);
        }
        let lines: Vec<String> = per_human
            .iter()
            .enumerate()
            .map(|(i, (turns, player, proof_backed, has_moves))| {
                format!(
                    "**#{}** `{}…` · {} turns attested · proof-backed: {} · moves stored: **{}**",
                    i + 1,
                    &player[..player.len().min(12)],
                    turns,
                    proof_backed,
                    has_moves,
                )
            })
            .collect();
        (lines, no_moves)
    })
    .unwrap_or_else(|_| (Vec::new(), true))
}

/// The channel's folds + a live one-word status each (for `/crown status`).
fn folds_in(channel: u64) -> Vec<(u64, Game, String)> {
    run(move |core| {
        let mut rows: Vec<(u64, Game, String)> = core
            .folds
            .iter()
            .filter(|(_, r)| r.channel == channel)
            .map(|(&t, r)| {
                let status = match (r.ranked.is_some(), r.job) {
                    (true, _) => "RANKED · the board holds the proof (and no moves)".to_string(),
                    // Unranked with no job: a restored row that failed to re-verify would not be
                    // here at all, so this is unreachable in practice — reported, not guessed.
                    (false, None) => "restored, with no live proving job".to_string(),
                    (false, Some(job)) => match core.service.status(job) {
                        JobStatus::Queued => "queued".to_string(),
                        JobStatus::Proving => "proving (the real fold · minutes)".to_string(),
                        JobStatus::Done(_) => {
                            "proof READY · press its status button to rank it".to_string()
                        }
                        JobStatus::Failed(e) => format!("failed: {}", truncate(&e, 120)),
                        JobStatus::Unknown => "unknown".to_string(),
                    },
                };
                (t, r.game, status)
            })
            .collect();
        rows.sort_by_key(|(t, _, _)| *t);
        rows
    })
    .unwrap_or_default()
}

// ─────────────────────────────────────────────────────────────────────────────
// Extracting the played match from the live `/play` session.
// ─────────────────────────────────────────────────────────────────────────────

/// The channel's finished automatafl match as a fold job — **the PLAYED two-leg chain**: the
/// genesis position plus every resolved round's two revealed moves
/// ([`AutomataflMatch::played`]), which folds as `Leg R` (the players' adjudicated moves) then
/// `Leg A` (the automaton's step) per round, board-window chained, with the root exposing the
/// decodable genesis and final positions.
///
/// This replaced `AutomataflMatch::automaton_only`, which the game-board crate's own doc says
/// "attests K INDEPENDENT automaton steps and no move at all" — a crown over that proved nothing
/// about how the match was played (and, at the old 5×5 board, could not be minted at all: there
/// is no emitted Lean descriptor at n=5).
///
/// ⚑ SCOPE, at the resolution the fold actually reaches. Two shapes are foldable and the third is
/// named, not faked:
///
/// 1. **every turn CLEAN** → `PlayedMatch::Automatafl` (the two-leg chain above), any number of
///    turns;
/// 2. **exactly ONE turn, and it RE-ENTERED** → `PlayedMatch::AutomataflTurn`, a real
///    [`MultiRoundTurn`] built from the surface's recorded per-round history: `k` Leg C conflict
///    rounds on the 32-lane RoundState window (accumulating the marks) welded to the terminating
///    marks-aware Leg RM + marks-carrying Leg A. This is the path the conflict protocol opened;
/// 3. **≥2 turns with a conflicted one among them** → REFUSED, by name. The clean-handoff root
///    admits exactly ONE width change (32 → 20), which is one conflicted turn's worth; there is no
///    assembler that chains a second turn's leaves onto that root. Folding it as the plain two-leg
///    chain instead would attest a transition in which the clash never happened, so it is refused.
fn played_automatafl(channel: u64) -> Option<PlayedMatch> {
    offering::with_live::<AutomataflOffering, _>(channel, |live| {
        if !live.session.ended() {
            return None;
        }
        // No resolved turn ⇒ no played transition to attest. Nothing is minted (the old path
        // would have folded an automaton-only chain that says nothing about the players).
        let turns = live.session.turns_played();
        if turns.is_empty() {
            return None;
        }
        // THE CONFLICT BRAID, when the match is one re-entered turn. `conflict_subs` is the
        // submissions of each conflict round in re-entry order — exactly `MultiRoundTurn`'s field —
        // and `clean_subs` the pair that finally resolved.
        if turns.len() == 1 && !turns[0].conflict_subs.is_empty() {
            let t = &turns[0];
            return Some(PlayedMatch::AutomataflTurn(MultiRoundTurn::new(
                t.start.clone(),
                t.conflict_subs.clone(),
                t.clean_subs,
            )));
        }
        Some(PlayedMatch::Automatafl(AutomataflMatch::played(
            live.session.start_board().clone(),
            live.session.rounds(),
        )))
    })
    .flatten()
}

/// ⚑ **WHY this channel's finished automatafl match cannot be folded, if it cannot** — the honest
/// refusal, computed HERE (before the prover is handed anything) rather than surfacing minutes later
/// as an opaque job failure.
///
/// One shape is genuinely blocked and it is blocked STRUCTURALLY, not for want of a witness: a match
/// of ≥2 turns one of which RE-ENTERED. Its leaf chain would change window width twice (the clean
/// turns' 20-lane two-leg rounds, the conflicted turn's 32-lane RoundState braid, and back), and the
/// deployed mixed-width root admits exactly ONE change. Folding it as the plain two-leg chain
/// instead is the trap: the terminating round of a re-entered turn IS clean, so the plain gate would
/// pass it and attest a transition in which the clash never happened. Refused by name.
///
/// The cleanliness half is put to the PROVEN LEAN (`dregg_automatafl::rules::round_is_clean`,
/// `@[export] dregg_automatafl_rules`) through the session's own
/// [`AutomataflSession::unfoldable_round`](dregg_automatafl::surface::AutomataflSession::unfoldable_round);
/// if the oracle cannot answer, the crown is refused rather than guessed.
fn automatafl_fold_block(channel: u64) -> Option<String> {
    offering::with_live::<AutomataflOffering, _>(channel, |live| {
        let turns = live.session.turns_played();
        let conflicted: Vec<usize> = turns
            .iter()
            .enumerate()
            .filter(|(_, t)| !t.conflict_subs.is_empty())
            .map(|(i, _)| i + 1)
            .collect();
        if !conflicted.is_empty() {
            if turns.len() == 1 {
                // The conflict braid IS the fold (`PlayedMatch::AutomataflTurn`). Its rounds are
                // gated leaf-by-leaf by the fail-closed Leg C witness canary, so nothing to add.
                return None;
            }
            return Some(format!(
                "This match has **{} turns**, and turn(s) **{}** went through the ruleset's \
                 conflict RE-SUBMISSION loop (the square was marked and the round re-opened). \
                 Both shapes fold on their own (a clash-free match through the two-leg chain, a \
                 single re-entered turn through the Leg C conflict braid), but not *together*: the \
                 deployed mixed-width root admits exactly ONE window-width change (32 → 20, the \
                 clean handoff), and a match that alternates clean turns with a re-entered one \
                 needs two.\n\n\
                 So this is REFUSED rather than mis-attested. Folding it as the plain chain would \
                 mint a succinct proof of a turn in which the clash never happened: the \
                 terminating round of a re-entered turn *is* clean, which is exactly why that trap \
                 has to be closed by name here.",
                turns.len(),
                conflicted
                    .iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            ));
        }
        match live.session.unfoldable_round() {
            Ok(None) => None,
            Ok(Some(i)) => Some(format!(
                "Turn **{}** of this match is not a clean round by the ruleset's own reckoning, so \
                 the two-leg fold refuses it rather than attest a transition the rules never \
                 licensed.",
                i + 1
            )),
            Err(why) => Some(format!(
                "The game oracle could not adjudicate this match, so nothing is attested: `{why}`."
            )),
        }
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
    let body = "This match is over, and every move of it is already a committed, verified \
        turn. Press the button and the whole match FOLDS, in the background, into **one \
        succinct proof**.\n\n\
        The proof goes on the game's board. The moves do not. **Your hand was fog to your \
        opponent and it stays fog forever**: the board stores the proof and *nothing else*, \
        and any stranger can re-check the entire match in **O(1)** (one light-client \
        verification, no replay, no trusting you, no trusting this bot).\n\n\
        *Prove you won. Reveal nothing about how.*";
    let msg = CreateMessage::new()
        .embed(crown_embed("👑 Prove you won, without revealing how", body))
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
        .description("Fold a finished match into ONE proof · prove you won without revealing how")
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
                    "No finished, WON `{}` match is live in this channel. Win one (`{}`) and \
                     the crown appears.",
                    game.slug(),
                    crate::commands::menus::open_invocation(offering_key_of(game)),
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
                     whole-match win leaf proves the *influence* path (`charm >= 11`), so this \
                     match is refused rather than mis-attested. Win on influence and the crown \
                     folds.",
                    w.charm,
                ))
                .color(COLOR_REFUSED),
            Vec::new(),
        );
    }
    // An automatafl match the fold cannot honestly attest is refused HERE, by name, rather than
    // shipped to the prover to fail opaquely minutes later — see [`automatafl_fold_block`] for which
    // shape is blocked and why. A single re-entered turn is no longer among them: it folds as the
    // Leg C conflict braid (`PlayedMatch::AutomataflTurn`).
    if matches!(
        m,
        PlayedMatch::Automatafl(_) | PlayedMatch::AutomataflTurn(_)
    ) && let Some(why) = automatafl_fold_block(channel)
    {
        return (
            CreateEmbed::new()
                .title("This match folds no crown (yet)")
                .description(why)
                .color(COLOR_REFUSED),
            Vec::new(),
        );
    }
    match enqueue_fold(game, channel, player_hex, m) {
        Enqueued::Token(token) => (
            crown_embed(
                &format!("👑 Fold #{token} enqueued · proving in the background"),
                &format!(
                    "The **{}** match is now folding into one `WholeChainProof` on the \
                     background prover pool. This is the real recursive STARK fold. It takes \
                     **minutes**, not milliseconds, and nothing here waits on it: the play is \
                     already over and committed.\n\n\
                     Press **Proving status** to poll. When the proof is ready it goes to the \
                     board: the proof, never the moves.",
                    game.title(),
                ),
            ),
            vec![status_button(token)],
        ),
        Enqueued::Already(token) => (
            crown_embed(
                &format!("Fold #{token} is already running for this match"),
                "One fold per match at a time; poll the one in flight.",
            ),
            vec![status_button(token)],
        ),
        Enqueued::QueueFull => (
            CreateEmbed::new()
                .title("The proving queue is full")
                .description(
                    "The bounded background pool refused a new job (drop, not block; the \
                     play already happened and loses nothing). Try again in a minute.",
                )
                .color(COLOR_REFUSED),
            Vec::new(),
        ),
    }
}

/// The honest card for a fold job the blocking pool dropped — never rendered as an enqueue that
/// worked, because the match is either folding or it is not, and this side does not know which.
fn dropped_job_card() -> (CreateEmbed, Vec<CreateActionRow>) {
    (
        CreateEmbed::new()
            .title("The fold could not be started")
            .description(
                "The crown service did not run the enqueue, so nothing here can honestly be \
                 called \"proving\". The match itself is untouched: every move of it is still a \
                 committed, verified turn. Check `/verify crown action:status` and try again.",
            )
            .color(COLOR_REFUSED),
        Vec::new(),
    )
}

/// The ranked crown post: embed + re-verify button + (on first rank) the proof envelope file.
fn ranked_post(game: Game, token: u64, facts: &Ranked) -> (CreateEmbed, Vec<CreateActionRow>) {
    let scope_line = match game {
        Game::MultiwayTug => {
            "The folded leaves are blinded Poseidon2 membership proofs: the proof's public \
             inputs are `[blinded_leaf, hand_root]`. **The winning hand was never revealed and \
             is not in this proof.**"
        }
        Game::Automatafl => {
            "The folded chain is the played BOARD chain: each round's adjudicated resolution (Leg \
             R / the marks-aware Leg RM) then the automaton's step (Leg A), board-window chained, \
             plus one Leg C leaf per conflict round when the turn went through the ruleset's \
             re-submission loop. The board transitions are proven; **no move list is posted \
             anywhere**."
        }
    };
    // ⚑ THE ANCHOR LINE IS NOT OPTIONAL AND IT IS NOT A FOOTNOTE. Whether this card may say
    // "you do not have to trust the winner" is decided entirely by where the anchor came from,
    // so the two are written together, in one match, and cannot drift apart.
    let anchor_line = match facts.anchor_provenance {
        AnchorProvenance::OperatorConfigured => format!(
            "**The anchor is not the winner's.** It is operator configuration \
             (`{env}`), held before this fold existed. You do not have to trust the winner. \
             You do not have to trust this bot: take the attached file and check it yourself.",
            env = dreggnet_game_board::env_var_name(game),
        ),
        AnchorProvenance::BootstrappedFromSubmission => format!(
            "⚠ **Read this before reading the rank.** No operator anchor is configured for this \
             board (`{env}` is unset), so its genesis root and its WIN root were taken from the \
             FIRST fold this board accepted and frozen there. Every fold since — including this \
             one — is checked against a definition of *winning* that a player supplied. So this \
             card says *this proof agrees with that first fold's claim about the game*; it does \
             NOT say you need not trust the winner. The proof itself is real and you can check it \
             yourself from the attached file — against whichever anchor **you** choose.",
            env = dreggnet_game_board::env_var_name(game),
        ),
    };
    let body = format!(
        "**{turns} turns attested** · rank **#{rank}** · proof envelope **{len} bytes** · \
         vk `{vk}…` · completion `{cid}…`\n\n\
        The board checked this proof in **O(1)**: one whole-history light-client run \
        against its pinned anchor (VK + genesis + WIN). It re-witnessed nothing, replayed \
        nothing, and stored **no moves**: `has_moves() == false` on every entry.\n\n\
        {scope}\n\n\
        The envelope is attached. **Anyone** may press *Re-verify* and watch this bot re-run \
        the same O(1) check on the stored proof, in public, or take the file and check it \
        themselves.\n\n\
        {anchor}",
        turns = facts.turns,
        rank = facts.rank,
        len = facts.proof_len,
        vk = facts.vk8,
        cid = hex::encode(&facts.completion_id[..4]),
        scope = scope_line,
        anchor = anchor_line,
    );
    (
        crown_embed(
            &format!(
                "👑 RANKED · the board holds a proof and NO moves ({} · fold #{token})",
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
            let player = identity_of(state, command.user.id.get()).0;
            // ACK FIRST — the fold is the other half of the `crown:status` lesson below. Picking
            // the game is itself two blocking store reads (`played_match_of` per crowned game),
            // and then `enqueue_response` REPLAYS the whole match through the proven Lean rules
            // oracle (`round_is_clean` + `apply_turn`, once per round) and hands `enqueue_fold` a
            // job on the background proving pool — minutes of real recursive STARK work, holding
            // one of a bounded number of slots. Every bit of it ran before the first response, so
            // losing the 3s race left the fold RUNNING and the folder told "This interaction
            // failed": no token, no status button, no reason to believe anything was happening.
            //
            // Selection and enqueue are ONE blocking job, so the match cannot end (or be replaced)
            // between choosing it and folding it.
            let done = ack::defer_slash_then(ctx, command, false, move || {
                // Whichever crowned game has a finished, won match live in this channel.
                let game = [Game::MultiwayTug, Game::Automatafl]
                    .into_iter()
                    .find(|g| played_match_of(*g, channel).is_some())?;
                Some(enqueue_response(game, channel, player))
            })
            .await;
            let (embed, rows) = match done {
                Some(Some(card)) => card,
                Some(None) => (
                    CreateEmbed::new()
                        .title("Nothing crowned to fold here")
                        // Derived: `/play tug` and `/play automatafl` were both pre-fold spellings
                        // AND missing `offering:`.
                        .description(format!(
                            "No finished, WON match is live in this channel. Win a `{tug}` or \
                             `{af}` match first, then fold it to one proof.",
                            tug = crate::commands::menus::open_invocation("tug"),
                            af = crate::commands::menus::open_invocation("automatafl"),
                        ))
                        .color(COLOR_REFUSED),
                    Vec::new(),
                ),
                None => dropped_job_card(),
            };
            ack::edit_slash(ctx, command, embed, rows).await;
        }
        "status" => {
            // A read, but a read that QUEUES behind whatever the crown board thread is doing —
            // including a fold enqueue. ACK first and take the blocking wait off the worker.
            let rows = ack::defer_slash_then(ctx, command, true, move || folds_in(channel))
                .await
                .unwrap_or_default();
            let body = if rows.is_empty() {
                "No folds in this channel yet. Win a match, then `/verify crown action:fold`."
                    .to_string()
            } else {
                rows.iter()
                    .map(|(t, g, s)| format!("**fold #{t}** ({}) · {s}", g.slug()))
                    .collect::<Vec<_>>()
                    .join("\n")
            };
            let buttons: Vec<CreateActionRow> = rows
                .iter()
                .take(5)
                .map(|(t, _, _)| status_button(*t))
                .collect();
            ack::edit_slash(
                ctx,
                command,
                crown_embed("👑 This channel's match folds", &body),
                buttons,
            )
            .await;
        }
        "board" => {
            let read = ack::defer_slash_then(ctx, command, false, || {
                [Game::MultiwayTug, Game::Automatafl].map(|g| (g, board_lines(g)))
            })
            .await;
            let mut body = String::new();
            for (game, (lines, no_moves)) in read.into_iter().flatten() {
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
            if body.is_empty() {
                body.push_str(
                    "_the board service did not answer; nothing here is a claim about what is \
                     ranked. Try again in a moment._",
                );
            }
            ack::edit_slash(
                ctx,
                command,
                crown_embed("👑 The proof-carrying game board", body.trim_end()),
                Vec::new(),
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
            // NEVER a silent drop: a fold button naming a game this build no longer serves used
            // to `return` without answering, and Discord printed "This interaction failed".
            let Some(game) = game_of_key(key) else {
                component_ephemeral(
                    ctx,
                    component,
                    // The shared stale-control stem with this press's own specific next step.
                    &dreggnet_offerings::refusal::stale_control(
                        "Run `/verify crown action:status` to see where your fold stands.",
                    ),
                )
                .await;
                return;
            };
            let player = identity_of(state, component.user.id.get()).0;
            // ACK FIRST, then replay + enqueue on the blocking pool (see the slash arm above:
            // this is a Lean match replay followed by a real proving-pool enqueue, and it also
            // bottoms out in a `sync_channel` `recv()` against the crown board thread AND the
            // offering store thread that every other player's move queues on).
            let done = ack::ack_component_then(ctx, component, move || {
                enqueue_response(game, channel, player)
            })
            .await;
            let (embed, rows) = done.unwrap_or_else(dropped_job_card);
            // Replace the offer message (its button has done its job; no double-enqueue bait).
            ack::edit_component(ctx, component, embed, rows).await;
        }
        [PREFIX, "status", tok] => {
            let Ok(token) = tok.parse::<u64>() else {
                component_ephemeral(
                    ctx,
                    component,
                    &dreggnet_offerings::refusal::stale_control(
                        "Run `/verify crown action:status` to see where your fold stands.",
                    ),
                )
                .await;
                return;
            };
            // ACK FIRST — AND THE CROWN IS WHY. `poll_fold` does not merely READ: on a finished
            // fold it runs the board's proof-accept path and MUTATES the record to ranked. That
            // whole verification ran before the first response, so a check that outran Discord's
            // 3s window ranked the fold and then died as "This interaction failed" — and the
            // public crown post, with its `.dreggproof` attachment, was LOST. Not delayed: lost.
            // A second press now takes the `AlreadyRanked` path and only whispers an ephemeral
            // line. Somebody won a match, the proof landed, and the channel never heard about it.
            //
            // The poll also runs OFF the async worker now: it is a `sync_channel` `recv()` on the
            // crown board thread, and on a finished fold the job it waits for is a whole
            // light-client proof verification. Blocking a Tokio worker on that put its latency on
            // every other in-flight interaction's 3-second clock at once.
            let polled = ack::ack_component_then(ctx, component, move || poll_fold(token)).await;
            let Some(polled) = polled else {
                ack::followup_ephemeral(
                    ctx,
                    component,
                    "The crown service did not answer the poll, so nothing here is a claim about \
                     this fold's state: it was NOT reported as failed and NOT reported as \
                     ranked. Press again in a moment.",
                )
                .await;
                return;
            };
            match polled {
                Poll::NoSuchFold => {
                    ack::followup_ephemeral(
                        ctx,
                        component,
                        "No such fold (the bot may have restarted; pending folds are \
                         in-process). Re-fold the match with `/verify crown action:fold`.",
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
                    ack::followup_ephemeral(
                        ctx,
                        component,
                        &format!(
                            "⏳ **Fold #{token}: proving in the background** · {phase} \
                             ({in_flight} fold(s) in flight on {workers} worker(s)). The real \
                             recursive fold takes minutes; press again later. Nothing is \
                             waiting on it: the match is already committed.",
                        ),
                    )
                    .await;
                }
                Poll::Failed(e) => {
                    ack::followup_ephemeral(
                        ctx,
                        component,
                        &format!(
                            "✗ **Fold #{token} failed · nothing was ranked.** The fold's own \
                             teeth: {e}",
                        ),
                    )
                    .await;
                }
                Poll::BoardRefused(e) => {
                    ack::followup_ephemeral(
                        ctx,
                        component,
                        &format!(
                            "✗ **The board REFUSED fold #{token}'s proof · nothing was \
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
                    // PUBLIC — the crown moment belongs to the channel. A followup now (the
                    // press was deferred above), which also leaves the pressed message intact:
                    // the crown post is a NEW message on purpose. A win is the one thing in this
                    // game that should still be in the channel tomorrow.
                    let _ = component
                        .create_followup(
                            &ctx.http,
                            serenity::all::CreateInteractionResponseFollowup::new()
                                .embed(embed)
                                .components(rows)
                                .add_file(file),
                        )
                        .await;
                }
                Poll::AlreadyRanked { game, facts } => {
                    ack::followup_ephemeral(
                        ctx,
                        component,
                        &format!(
                            // `/crown` folded under `/verify` and this pointer did not follow it.
                            "👑 Fold #{token} ({}) is already RANKED · {} turns attested, \
                             rank #{}. Press **Re-verify** on its crown post (or run \
                             `/verify crown action:board`).",
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
                        &format!("✓ Re-checked in O(1) · fold #{token} ({})", game.slug()),
                        &format!(
                            "The whole-history light client just re-checked the **stored** \
                             proof against the board's pinned anchor: **{turns} turns \
                             attested**, genesis → WIN, completion `{}…`.\n\n\
                             No move was replayed. None exists to replay: the board stores \
                             the proof and nothing else. That is the crown: *anyone* can do \
                             what just happened, in one cheap check, forever.\n\n\
                             ⚑ Against WHICH anchor: {}.",
                            hex::encode(&facts.completion_id[..4]),
                            facts.anchor_provenance.sentence(game),
                        ),
                    ),
                    vec![reverify_button(token)],
                ),
                Err(e) => (
                    CreateEmbed::new()
                        .title(format!("✗ Re-verify refused · fold #{token}"))
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

    /// **THE FOLD IS ENQUEUED AFTER THE ANSWER.**
    ///
    /// `enqueue_response` is not a render — it REPLAYS the whole match through the proven Lean
    /// rules oracle (`round_is_clean` + `apply_turn`, once per round) and then `enqueue_fold`
    /// blocks on the crown board thread to put a job on the background proving pool: minutes of
    /// real recursive STARK work, holding one of a bounded number of slots. Both the slash `fold`
    /// and the win-moment button ran all of that before their first Discord response, so a fold
    /// that outran the 3-second window was RUNNING while the folder was told "This interaction
    /// failed" — with no token, no status button, and no reason to think anything was happening.
    ///
    /// This drives the REAL `enqueue_response` through the REAL ordering helper the two handlers
    /// use. The trace is the assertion; restore the work-first ordering and it inverts.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn a_fold_is_answered_before_it_reaches_the_proving_pool() {
        use std::sync::{Arc, Mutex};
        // Deliberately NOT `boot_the_test_board()`. What is under test is the ORDERING, and
        // `enqueue_response` reaches its answer through `played_match_of` on an empty channel —
        // it needs no ranked board and no fixture. Installing one only borrows that fixture's
        // problems: it currently panics at load ("the shipped fixture proof verifies:
        // AggregateInvalid(EnvelopeDecode …)"), which is the restart-gate's own red and has
        // nothing to say about whether this handler answers before it works.
        let trace: Arc<Mutex<Vec<&'static str>>> = Arc::new(Mutex::new(Vec::new()));

        let ack_trace = Arc::clone(&trace);
        let work_trace = Arc::clone(&trace);
        let card = crate::commands::ack::testing::ack_then_blocking_for_test(
            async move {
                tokio::task::yield_now().await;
                ack_trace.lock().unwrap().push("acked");
            },
            move || {
                let out = enqueue_response(Game::Automatafl, 0xC0_0001, "aa".repeat(32));
                work_trace.lock().unwrap().push("enqueued");
                out
            },
        )
        .await;

        assert!(card.is_some(), "the enqueue job must run to completion");
        assert_eq!(
            trace.lock().unwrap().as_slice(),
            ["acked", "enqueued"],
            "the match was replayed and handed to the proving pool before Discord was told \
             anything — lose that race and the fold runs orphaned"
        );
    }

    /// A fold job the blocking pool drops is NEVER painted as an enqueue that worked: the match
    /// is either folding or it is not, and this side does not know which.
    #[test]
    fn a_dropped_fold_job_does_not_claim_to_be_proving() {
        let (embed, rows) = dropped_job_card();
        assert!(rows.is_empty(), "a dropped job offers no status button");
        let rendered = format!("{:?}", embed);
        assert!(
            !rendered.contains("proving in the background"),
            "a dropped job must not be dressed as a live fold: {rendered}"
        );
        assert!(rendered.contains("could not be started"), "{rendered}");
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

    /// **Panic isolation**: a job that panics on the crown-board thread does NOT brick the board.
    /// Before this hardening a panicking job killed the thread and every later `/crown` press
    /// panicked at `send`/`recv`'s `.expect`; now the panic is contained (this caller gets a clean
    /// `Err`) and a subsequent job on the same board still succeeds. (An expected contained
    /// "panicked at 'crown-panic-isolation-canary'" line on stderr is the point, not a failure.)
    #[test]
    fn a_panicking_job_does_not_brick_the_board() {
        // Share the one process-global boot with the restart test — whichever runs first
        // installs the fixture store, so neither can spawn the board thread behind the other's
        // back and skip the restore.
        boot_the_test_board();
        let panicked: Result<(), StoreError> = run(|_core| panic!("crown-panic-isolation-canary"));
        assert!(
            panicked.is_err(),
            "a panicking job must return an Err, not abort the caller"
        );
        // The board thread SURVIVED: the next job still answers. (The fold COUNT is now
        // boot-dependent — the board restores persisted crowns on spawn — so the assertion is
        // "it still serves", which is what this test was ever about.)
        let folds = run(|core| core.folds.len());
        assert!(
            folds.is_ok(),
            "the board thread must survive a panicking job and keep serving"
        );
    }

    // ─────────────────────────────────────────────────────────────────────────
    // 👑 THE RESTART GATE — a public crown post's Re-verify button, after a reboot.
    // ─────────────────────────────────────────────────────────────────────────

    /// A [`CrownStore`] backed by a fixed set of rows, standing in for "what sqlite held when
    /// the process came up". (The sqlite impl's own round-trip is tested in `crown_store`; what
    /// is under test HERE is the board's re-verify-and-restore, which is the part that decides
    /// whether a stranger's button works tomorrow.)
    struct FixtureCrownStore {
        rows: Vec<StoredCrownFold>,
    }

    impl CrownStore for FixtureCrownStore {
        fn persist_fold(&self, _fold: &StoredCrownFold) -> Result<(), String> {
            Ok(())
        }
        fn list_folds(&self) -> Result<Vec<StoredCrownFold>, String> {
            Ok(self.rows.clone())
        }
    }

    /// The REAL folded whole-history proof this tree ships (`ugc-dregg`'s in-tree 3-turn
    /// recursive fold) plus the VK it verifies under. A genuine artifact of the deployed prover
    /// — never a stub. It is not a *game match* (folding one is minutes-to-hours; that is the
    /// game-board crate's own `--ignored` lane), and the same substitution is what
    /// `dreggnet-game-board`'s fast board tests make for the same reason. What it exercises here
    /// is exactly what a restored crown needs to be true: the board re-opens against a persisted
    /// anchor and the light client accepts the persisted envelope against it.
    fn real_proof() -> (Vec<u8>, [u8; 32]) {
        let dir =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../ugc-dregg/tests/fixtures");
        let bytes = std::fs::read(dir.join("whole_history_proof.bin"))
            .expect("the in-tree real whole-history proof fixture");
        let anchor = std::fs::read_to_string(dir.join("whole_history_anchor.hex"))
            .expect("the fixture's anchor VK");
        let vk: [u8; 32] = hex::decode(anchor.trim())
            .expect("the anchor is hex")
            .try_into()
            .expect("the anchor is 32 bytes");
        (bytes, vk)
    }

    /// The ONE persisted crown this test process boots with — built from the real proof, with
    /// the anchor read off the light client's own attestation of it (exactly what
    /// `persist_fold` writes at rank time).
    ///
    /// `None` when the shared fixture does not verify under HEAD. That is a REAL failure of the
    /// tree, not of the crown, and it is separated from a panic here on purpose: the tests that
    /// merely need *a board* (panic isolation) stay green and keep their signal, while the ones
    /// that genuinely need a verifying proof go red through [`require_fixture_fold`] with the
    /// reason spelled out. Silently skipping them instead would be a gate that cannot go red.
    fn fixture_fold() -> Option<StoredCrownFold> {
        let (proof, vk) = real_proof();
        let attested = dregg_lightclient::verify_history_bytes(&proof, &RecursionVk(vk)).ok()?;
        Some(StoredCrownFold {
            token: 41,
            game: Game::Automatafl.slug().to_string(),
            channel: 777,
            player: "cc".repeat(32),
            turns: attested.num_turns,
            vk,
            genesis_root: attested.genesis_root.map(|f| f.0),
            win_root: attested.final_root.map(|f| f.0),
            proof,
        })
    }

    /// [`fixture_fold`] or a LOUD, actionable failure. A stale fixture fails
    /// `verify_history_bytes` with `EnvelopeDecode`, which reads exactly like a light-client
    /// regression; this names what it actually is and how to fix it, the same tooth
    /// `dreggnet-game-board/tests/support/mod.rs` grew over the same file.
    fn require_fixture_fold() -> StoredCrownFold {
        let (proof, vk) = real_proof();
        let reason = match dregg_lightclient::verify_history_bytes(&proof, &RecursionVk(vk)) {
            Ok(_) => return fixture_fold().expect("it just verified"),
            Err(e) => e,
        };
        panic!(
            "the shared whole-history proof fixture does not verify under HEAD ({reason:?}), so \
             this test cannot be satisfied. This is NOT a crown regression — the crown's own \
             plumbing is covered by `crown_store` and by the anchor/refusal tests. Re-bake the \
             fixture: `DREGG_ALLOW_UNAUDITED_PQ=1 cargo run --release -p dregg-lightclient --bin \
             produce_history_envelope --features prover -- 3 7`, base64-decode the emitted \
             `proof_bytes_b64` into ugc-dregg/tests/fixtures/whole_history_proof.bin and write \
             `anchor_hex` (no trailing newline) to whole_history_anchor.hex. The producer used to \
             fail at HEAD itself with \
             `RecursionFailed(InvalidOpeningArgument(InputError(CapMismatch)))` (measured \
             2026-07-25), which made the re-bake impossible; that is FIXED — it ran clean on \
             2026-07-26 and produced the fixture in the tree now, so the command above is the \
             whole fix."
        )
    }

    // ── RESTART SEMANTICS for the crown's token counter + anchor pin ─────────────
    //    (docs/reference/RESTART-SEMANTICS.md — answer 2, REBUILD)
    //
    // `next_token` is REBUILT from the durable rows at boot. It used to advance only in the
    // `Ok` arm of the restore loop, so a row that did not re-verify left the counter BELOW a
    // token already on disk. The next live fold minted that token, `INSERT OR IGNORE` dropped
    // its row, `persist_crown_fold` returned `Ok(())`, and the "RANKED but did not persist"
    // warning could never fire — a public crown silently un-persisted.

    /// A fresh restore target (what `restore_rows` writes into) — no proving pool, no store.
    fn restore_target() -> (
        GameBoard,
        BTreeMap<Game, (ProofAnchor, AnchorProvenance)>,
        HashMap<u64, FoldRecord>,
        u64,
    ) {
        (GameBoard::new(), BTreeMap::new(), HashMap::new(), 1)
    }

    /// A persisted row that will NOT re-verify: real shape, junk envelope.
    fn unverifiable_row(token: u64, game: Game) -> StoredCrownFold {
        StoredCrownFold {
            token,
            game: game.slug().to_string(),
            channel: 5,
            player: "dd".repeat(32),
            turns: 3,
            vk: [0x11; 32],
            genesis_root: [1, 2, 3, 4, 5, 6, 7, 8],
            win_root: [9, 10, 11, 12, 13, 14, 15, 16],
            proof: vec![0xFF; 64],
        }
    }

    /// ⚑ **A REFUSED ROW STILL SPENDS ITS TOKEN.** Boot restore over rows the board rejects must
    /// still leave `next_token` above every token on disk — otherwise the next live fold reuses
    /// one and its `INSERT OR IGNORE` row is dropped.
    #[test]
    fn a_persisted_row_that_does_not_reverify_still_reserves_its_token() {
        let (mut board, mut anchors, mut folds, mut next_token) = restore_target();
        restore_rows(
            &mut board,
            &mut anchors,
            &mut folds,
            &mut next_token,
            vec![
                unverifiable_row(7, Game::Automatafl),
                unverifiable_row(12, Game::MultiwayTug),
                // A row naming a game this build does not know — the other `continue` arm.
                StoredCrownFold {
                    game: "nonesuch".to_string(),
                    ..unverifiable_row(30, Game::MultiwayTug)
                },
            ],
        );
        assert!(
            folds.is_empty(),
            "none of these rows verify, so none may be restored"
        );
        assert_eq!(
            next_token, 31,
            "every token on disk is SPENT, verified or not — a refused row must not leave the \
             counter where a live fold would collide with it"
        );
        assert!(
            anchors.is_empty(),
            "a row that cannot verify against its own stored anchor must not PIN the board"
        );
    }

    /// The anchor pin survives a bad first row: a corrupt row must not freeze a game's board on
    /// its trust root and refuse every honest crown behind it.
    #[test]
    fn a_corrupt_first_row_does_not_pin_the_board_anchor() {
        let Some(good) = fixture_fold() else {
            // The shared fixture is what makes the NON-VACUOUS half of this test possible; a
            // stale one is a tree failure reported by `require_fixture_fold` elsewhere, and this
            // test still carries its own tooth via `require_fixture_fold` below.
            let _ = require_fixture_fold();
            unreachable!("require_fixture_fold panics when fixture_fold is None");
        };
        let (mut board, mut anchors, mut folds, mut next_token) = restore_target();
        // A corrupt row for the SAME game arrives FIRST (lower token = restored first).
        let mut corrupt = unverifiable_row(1, Game::Automatafl);
        corrupt.vk = [0xAB; 32]; // an attacker-chosen trust root
        restore_rows(
            &mut board,
            &mut anchors,
            &mut folds,
            &mut next_token,
            vec![corrupt, good.clone()],
        );
        assert_eq!(
            anchors.get(&Game::Automatafl).map(|(a, _)| a.vk.0),
            Some(good.vk),
            "the board must pin the HONEST row's anchor, not the corrupt row's"
        );
        assert!(
            folds.contains_key(&good.token),
            "the honest crown behind a corrupt row must still restore"
        );
        assert!(next_token > good.token, "tokens are still all reserved");
    }

    /// Install the fixture store and force the board thread to spawn + restore. Process-global
    /// and idempotent (`install_store` is a `OnceLock`), so every crown test funnels through it.
    /// An unverifiable fixture installs an EMPTY store rather than panicking — see
    /// [`fixture_fold`].
    fn boot_the_test_board() {
        static BOOTED: OnceLock<()> = OnceLock::new();
        BOOTED.get_or_init(|| {
            install_store(Box::new(FixtureCrownStore {
                rows: fixture_fold().into_iter().collect(),
            }));
        });
    }

    /// **THE CROWN SURVIVES A RESTART.**
    ///
    /// The concrete bug: a crown post is PUBLIC, carries a `.dreggproof` file and a "Re-verify
    /// (anyone, O(1))" button, and the board that button re-verifies against lived only in RAM.
    /// After any restart `reverify_fold` hit `None` in `core.folds` and returned
    /// `Err("no such fold")`, so the post rendered "✗ Re-verify refused." — a public artifact
    /// silently withdrawing its own verification affordance.
    ///
    /// This drives the exact button. A FRESH process (this test binary) has never ranked
    /// anything; the only thing it has is what the durable store held. It must:
    ///
    ///   * find fold #41 at all (the token a pre-restart button carries is restored EXACTLY);
    ///   * and answer `Ok` — meaning `reverify_entry` re-ran the whole-history light client over
    ///     the STORED envelope against the pinned anchor and it verified.
    ///
    /// Note what is NOT being asserted: nothing here trusts the stored row. The restore path
    /// re-submits through `GameBoard::submit_bytes`, which is the same O(1) accept path a live
    /// submission takes (light client + genesis binding + WIN binding + claimed-turns binding).
    /// A row that failed any of those would not be on the board and this would fail.
    #[test]
    fn a_ranked_crown_reverifies_after_a_restart() {
        // Resolve the fixture FIRST, so a stale one fails with its own actionable message
        // instead of surfacing as an inscrutable "no such fold" from the board.
        let expected = require_fixture_fold();
        boot_the_test_board();

        let (game, turns, facts) = reverify_fold(41).unwrap_or_else(|e| {
            panic!(
                "the Re-verify button on a crown posted before the restart must still work — \
                 got: {e}"
            )
        });
        assert_eq!(game, Game::Automatafl);
        assert_eq!(
            turns, expected.turns,
            "the re-verification re-attests the SAME turn count the crown post claimed",
        );
        assert_eq!(facts.turns, expected.turns);
        assert_eq!(facts.proof_len, expected.proof.len());

        // And the restored entry is on the board with the property the crown exists to show:
        // proof-backed, and storing NO moves.
        let (lines, no_moves) = board_lines(Game::Automatafl);
        assert!(
            !lines.is_empty(),
            "the restored crown is ranked on the board"
        );
        assert!(
            no_moves,
            "a restored entry is the proof envelope and nothing else — no moves came back \
             because none were ever stored",
        );
    }

    /// A TAMPERED persisted crown does not come back. The restore path is a re-verification, not
    /// a restoration of trust: flipping bytes in the stored envelope makes the light client
    /// refuse, and the fold is simply absent — its button keeps saying refused, which is the
    /// honest answer for a proof that no longer verifies.
    #[test]
    fn a_tampered_persisted_crown_is_refused_on_restore() {
        let mut fold = require_fixture_fold();
        // Flip a byte deep inside the proof envelope (past the header, so the failure is the
        // light client's verdict, not a decode error).
        let mid = fold.proof.len() / 2;
        fold.proof[mid] ^= 0xFF;

        // Drive the accept path directly against a PRIVATE board, so the process-global one this
        // test binary boots with is untouched. This is the exact call `restore_folds` makes.
        let mut board = GameBoard::new();
        board.ensure_open(Game::Automatafl, fold.anchor());
        let refused = board.submit_bytes(
            Game::Automatafl,
            &fold.player,
            fold.proof.clone(),
            fold.turns,
        );
        assert!(
            refused.is_err(),
            "a tampered envelope must be REFUSED by the same O(1) gate a live submission \
             faces — never restored on the strength of having been stored",
        );
        assert!(
            board.leaderboard(Game::Automatafl).is_empty(),
            "nothing was ranked",
        );
    }

    /// ⚑ **THE PERMANENT CONTROL: the card may not tell a stranger to trust a ranking whose
    /// anchor a player supplied.**
    ///
    /// Measured 2026-07-30: `ranked_post` printed *"You do not have to trust the winner."* on
    /// every crown, while `canonical_anchor` returned `None` unconditionally and the board's
    /// genesis and WIN roots therefore came from the FIRST fold's own wire and froze there.
    /// The winner defined winning.
    ///
    /// This drives the real renderer on both provenances and asserts the two sentences are
    /// mutually exclusive. Reinstate the unconditional line — or drop the `⚠` arm — and it
    /// goes red. It needs no proving pool and no fixture: the card is a pure function of
    /// `Ranked`, which is why the provenance is carried there.
    #[test]
    fn the_public_card_claims_winner_independence_only_when_an_operator_pinned_the_anchor() {
        fn facts(p: AnchorProvenance) -> Ranked {
            Ranked {
                universe: UniverseId::from_bytes([0u8; 32]),
                completion_id: [0u8; 32],
                turns: 9,
                rank: 1,
                proof_len: 4096,
                vk8: "deadbeef".to_string(),
                anchor_provenance: p,
            }
        }

        let (boot, _) = ranked_post(
            Game::Automatafl,
            7,
            &facts(AnchorProvenance::BootstrappedFromSubmission),
        );
        let boot_txt = format!("{boot:?}");
        assert!(
            !boot_txt.contains("You do not have to trust the winner"),
            "a board pinned to a submitted fold's own anchor may NOT tell a reader they need \
             not trust the winner — the winner chose the anchor"
        );
        assert!(
            boot_txt.contains("No operator anchor is configured")
                && boot_txt.contains("CROWN_ANCHOR_AUTOMATAFL"),
            "the card must say WHY the weaker claim, and how an operator fixes it"
        );
        assert!(
            boot_txt.contains("check it yourself"),
            "what a reader CAN still do must survive: the envelope is attached either way"
        );

        let (pinned, _) = ranked_post(
            Game::Automatafl,
            7,
            &facts(AnchorProvenance::OperatorConfigured),
        );
        let pinned_txt = format!("{pinned:?}");
        assert!(
            pinned_txt.contains("You do not have to trust the winner"),
            "an operator-pinned board earns the strong claim — a gate that cannot go green is \
             not a gate either"
        );
        assert!(
            !pinned_txt.contains("No operator anchor is configured"),
            "the two arms must be mutually exclusive"
        );
    }

    /// **A RESTART PRESERVES THE BOARD'S PINNED TRUST ANCHOR.**
    ///
    /// The anchor is the leaderboard's whole trust root: `submit_bytes` verifies every proof
    /// against it, so a board that comes up with the WRONG anchor either refuses honest folds or —
    /// far worse — ranks against an anchor a submitter chose. [`canonical_anchor`] ships no baked
    /// anchor yet, so the live board BOOTSTRAPS one from the first honest fold and freezes it; the
    /// only thing that carries that decision across a restart is the persisted row's own
    /// `vk`/`genesis_root`/`win_root` columns being re-pinned by [`restore_folds`].
    ///
    /// That is the property here, and it is distinct from
    /// `a_ranked_crown_reverifies_after_a_restart`: that test proves a fold re-verifies (which a
    /// correct anchor makes possible), this one reads the pinned anchor back and compares it, limb
    /// for limb, against what was on disk. Drop the anchor columns and re-mint the anchor from the
    /// submitted proof and this goes red while a re-verification test could still pass.
    #[test]
    fn a_restart_restores_the_pinned_board_anchor() {
        boot_the_test_board();

        // The anchor the board is actually pinned to, reduced to comparable limbs (`ProofAnchor`
        // is deliberately not `PartialEq` — it is configuration, not a value to shuffle around).
        let pinned = run(|core| {
            core.anchors
                .get(&Game::Automatafl)
                .map(|(a, _)| (a.vk.0, a.genesis_root.map(|f| f.0), a.win_root.map(|f| f.0)))
        })
        .expect("the crown board thread answers");

        let row = require_fixture_fold();
        assert_eq!(
            pinned,
            Some((row.vk, row.genesis_root, row.win_root)),
            "the board must come up pinned to the anchor its persisted crown was ranked under — \
             an anchor that is re-minted from a submitted proof, or lost with the process, hands \
             the leaderboard's trust root to whoever folds first after a reboot",
        );
    }
}
