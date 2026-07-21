//! # The games' FULL-STARK ASYNCHRONOUS LEADERBOARD
//!
//! **A played match folds to ONE succinct proof, which is submitted asynchronously to the
//! proof-carrying no-cheat board — verified there in O(1), the moves NEVER posted.**
//!
//! This is the crown made real for the two portfolio games. It adds no crypto and no game
//! rules: it is the BRIDGE between three committed things.
//!
//! ```text
//!   PLAY (fast, local)          PROVE (slow, background)        SUBMIT (a proof, not moves)
//!   ─────────────────           ────────────────────────        ───────────────────────────
//!   multiway-tug: a hand,       leaves ──fold_match──▶          ProofCompletion{ proof_bytes }
//!     membership-proven plays     ONE WholeChainProof                    │
//!   automatafl:  a board,       (dregg_multiway_tug::fold)               ▼
//!     automaton-step turns                                       ugc-dregg Registry
//!            │                            │                    ::submit_proof  ── O(1) ──▶
//!            └────── leaves ──────────────┘                    verify_history_bytes
//!                                                                     │
//!                                                       RANKED entry: proof + attested
//!                                                       publics, has_moves() == false
//! ```
//!
//! ## The three legs
//!
//! 1. **A played match → foldable leaves.** [`TugMatch`] turns a real hidden-hand match (a
//!    committed [`HandTree`](dregg_multiway_tug::HandTree) + the ordered plays + the
//!    terminal win) into the membership-proven [`LeafBundle`]s the game's own Phase-3 fold
//!    consumes. [`AutomataflMatch`] turns a real board + its automaton-step turns into the
//!    game's committed D1 Custom leaves. Both land on the SAME `LeafBundle` — so both games
//!    fold through ONE path ([`prove_match`] → [`dregg_multiway_tug::fold::fold_match`] →
//!    `prove_turn_chain_recursive`).
//! 2. **The proof → the proof-carrying board.** [`match_anchor`] pins a game's
//!    [`ProofAnchor`] (the light-client VK + the genesis anchor + the **WIN** anchor);
//!    [`GameBoard::open`] publishes the game's board universe against it, and
//!    [`GameBoard::submit`] hands the proof to `ugc_dregg::Registry::submit_proof`, which
//!    verifies it in O(1) (`verify_history_bytes`), re-witnessing nothing, and ranks it. The
//!    accepted [`Entry`] stores the proof envelope + the attested publics and **no moves**.
//! 3. **The async shape.** [`ProvingService`] models the real deployment: play is
//!    interactive-fast, the fold is minutes-to-hours, so a match is ENQUEUED
//!    ([`ProvingService::enqueue`]) and proven on a background worker; the player polls
//!    ([`ProvingService::status`]) and, when the proof is [`JobStatus::Ready`], submits it.
//!    The board never waits on, and never needs, the moves.
//!
//! ## What ranks, and what is never revealed
//!
//! * A **multiway-tug** match ranks with the **hand never revealed**: each play is a
//!   Poseidon2 membership leaf whose public inputs are `[blinded_leaf, hand_root]` — the
//!   card ids are not in the proof, and the siblings are hashes.
//! * An **automatafl** match ranks with the **moves never posted**: the board transition is
//!   proven by the D1 AIR (`new == automaton_step(old)`); only the fold's endpoints and the
//!   turn count are attested.
//!
//! ## Honest scope
//!
//! REAL (driven, non-vacuous): a played match of either game → the deployed recursive fold →
//! ONE `WholeChainProof` → the proof-carrying board's O(1) accept-path → a ranked entry with
//! `has_moves() == false`; a forged proof (a relabeled root) is REJECTED by the light client;
//! the anchor binds the VK + genesis + WIN root, so a proof for a different game/universe is
//! refused; the async play/prove/submit flow.
//!
//! NAMED RESIDUALS (not built here):
//! * **automatafl's full-match fold beyond D1's shape.** The folded automatafl chain is the
//!   committed D1 leaf (the automaton-step transition). The D2/D3 stages
//!   (`build_d2`/`build_d3` — player moves + conflict resolution) exist in `dregg-automatafl`
//!   and lower identically, but the *match* driven here is the D1-shaped chain.
//! * **On-device (wasm) proving.** The fold runs wherever [`ProvingService`] runs — a
//!   server-side worker here. "The moves never leave the device" needs the prover compiled to
//!   the client (wasm), which is a separate workstream.
//! * **True crypto-ZK.** The deployed STARK is *succinct*, not *hiding*. "Moves not posted"
//!   is a **data-availability** privacy property (nobody publishes them; the board never sees
//!   them), NOT a cryptographic hiding claim about the transcript.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{Sender, channel};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::RecursionVk;
use dregg_lightclient::{AttestedHistory, LightClientError, verify_history_bytes};

use dregg_automatafl::build_d1_honest;
use dregg_automatafl::reference::{Board, automaton_step};
use dregg_multiway_tug::hidden_hand::HandTree;

pub mod native_descent_board;

pub use dregg_multiway_tug::fold::{LeafBundle, fold_match, membership_leaf_for_play};
pub use ugc_dregg::{
    Accepted, Entry, ProofAnchor, ProofCompletion, Registry, RejectReason, Universe, UniverseId,
    WinCondition,
};

// ═══════════════════════════════════════════════════════════════════════════════
// The portfolio games.
// ═══════════════════════════════════════════════════════════════════════════════

/// A portfolio game with a proof-carrying board.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Game {
    /// The 2-player tug-of-influence card game — a match ranks with the HAND never revealed.
    MultiwayTug,
    /// The verified n=2 automatafl board — a match ranks with the MOVES never posted.
    Automatafl,
}

impl Game {
    /// The stable slug (the board universe's author-facing name component).
    pub fn slug(self) -> &'static str {
        match self {
            Game::MultiwayTug => "multiway-tug",
            Game::Automatafl => "automatafl",
        }
    }

    /// The board universe's display title.
    pub fn title(self) -> &'static str {
        match self {
            Game::MultiwayTug => "Multiway Tug — Proof Board",
            Game::Automatafl => "Automatafl — Proof Board",
        }
    }

    /// The minimal spween scene the board universe is published from. The proof path NEVER
    /// replays it (a `ProofCompletion` carries no moves) — the universe exists to be the
    /// content-addressed key the game's [`ProofAnchor`] is pinned to, and `ugc-dregg`
    /// requires a real, deployable world to publish.
    fn scene(self) -> String {
        format!(
            "---\nid: game-board-{slug}\ntitle: {title}\nweight: 1\n---\n\n=== start\n\n* [The match is proven off-board]\n  -> END\n",
            slug = self.slug(),
            title = self.title(),
        )
    }
}

impl fmt::Display for Game {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.slug())
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// (1) A PLAYED MATCH → the foldable leaves.
// ═══════════════════════════════════════════════════════════════════════════════

/// Why a played match could not be lowered to foldable leaves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MatchError {
    /// A played card is not under the current (remaining) hand root — never dealt, or already
    /// played. The hidden-hand membership tooth refusing a fabricated play.
    NotInHand(u64),
    /// The membership lowering refused the play (a tampered path that does not climb to the
    /// committed root).
    Lowering(String),
    /// An automatafl step's honest D1 witness did not self-accept (the AIR refused it).
    D1Refused(usize),
    /// The match has no turns — there is nothing to fold.
    Empty,
}

impl fmt::Display for MatchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatchError::NotInHand(c) => write!(f, "card {c} is not under the current hand root"),
            MatchError::Lowering(e) => write!(f, "membership lowering refused the play: {e}"),
            MatchError::D1Refused(i) => write!(f, "automatafl step {i}: the D1 AIR self-rejected"),
            MatchError::Empty => write!(f, "the match has no turns to fold"),
        }
    }
}

impl std::error::Error for MatchError {}

/// The terminal WIN/score turn of a multiway-tug match — the win as a **bound public output**
/// (`[charm, winner]`), proven by the range gadget (`charm >= 11`) with a conserved score.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TugWin {
    /// The winner's total influence — must clear the game's threshold (11).
    pub charm: u64,
    /// The winning player's id (1 or 2). Bound into the leaf's public-input commitment.
    pub winner: u64,
}

/// A **PLAYED multiway-tug match**: the dealt (secret) hand, the ordered plays, and the
/// terminal win. This is the player's PRIVATE record; only its fold leaves ever leave.
#[derive(Clone, Debug)]
pub struct TugMatch {
    /// The dealt hand — `(card_id, blinding nonce)` pairs. SECRET; never published.
    pub hand: Vec<(u64, u64)>,
    /// The ordered plays (card ids), each proven under the CURRENT remaining-hand root — so a
    /// replayed card fails membership (no double-play).
    pub plays: Vec<u64>,
    /// The terminal win/score turn, if the match was won.
    pub win: Option<TugWin>,
}

impl TugMatch {
    /// Lower the played match to the foldable leaves: one Poseidon2 **membership** leaf per
    /// play (public inputs `[blinded_leaf, hand_root]` — the card id is NOT among them), then
    /// the terminal win leaf if the match was won.
    ///
    /// A card not under the current remaining-hand root has no leaf ([`MatchError::NotInHand`])
    /// — the hidden-hand tooth refusing a fabricated or replayed play.
    pub fn leaves(&self) -> Result<Vec<LeafBundle>, MatchError> {
        let mut tree = HandTree::commit(self.hand.clone());
        let mut out = Vec::with_capacity(self.plays.len() + 1);
        for &card in &self.plays {
            let proof = tree.prove_play(card).ok_or(MatchError::NotInHand(card))?;
            let leaf = membership_leaf_for_play(&proof).map_err(MatchError::Lowering)?;
            out.push(leaf.into());
            // The play consumes the card: the next play proves against the UPDATED root.
            tree = tree.without(card);
        }
        if let Some(w) = self.win {
            out.push(win_leaf(w));
        }
        if out.is_empty() {
            return Err(MatchError::Empty);
        }
        Ok(out)
    }

    /// The committed hand root the match's first play proves under (the only thing about the
    /// hand that is ever public).
    pub fn hand_root(&self) -> [u8; 32] {
        HandTree::commit(self.hand.clone()).root_bytes()
    }
}

/// The terminal win/score leaf: a `game-turn-slice` range-gadget program proving the winner
/// crossed the influence threshold (`FieldGte charm >= 11`) with a conserved score
/// (`new[score] == old[score] + new[points]`), binding `[charm, winner]` as the leaf's public
/// inputs — so the WIN is a bound public output the fold carries (mirrors the committed
/// `dregg_multiway_tug::fold` win-turn shape).
fn win_leaf(w: TugWin) -> LeafBundle {
    use dregg_cell::program::{StateConstraint, field_from_u64};
    use game_turn_slice::compiler::{GameProgramCompiler, SlotAssignment};

    const WIN_CHARM: u8 = 0;
    const WIN_SCORE: u8 = 1;
    const WIN_POINTS: u8 = 2;

    let mut c = GameProgramCompiler::new("multiway-tug-win-v1", 16).with_public_inputs(2);
    c.lower_state_constraint(&StateConstraint::SumEqualsAcross {
        input_fields: vec![WIN_SCORE],
        output_fields: vec![WIN_POINTS],
    })
    .expect("score conservation lowers");
    c.lower_state_constraint(&StateConstraint::FieldGte {
        index: WIN_CHARM,
        value: field_from_u64(11),
    })
    .expect("the win threshold lowers via the range gadget");
    let program = c.finish();
    let assign = SlotAssignment::new()
        .set_new(WIN_CHARM, w.charm)
        .set_new(WIN_SCORE, 20)
        .set_old(WIN_SCORE, 15)
        .set_new(WIN_POINTS, 5); // 20 - 15 - 5 == 0
    let witness_values = c.witness(&assign, 4).expect("honest win witness");
    LeafBundle {
        program,
        witness_values,
        num_rows: 4,
        public_inputs: vec![BabyBear::from_u64(w.charm), BabyBear::from_u64(w.winner)],
    }
}

/// A **PLAYED automatafl match**: the starting board and the number of automaton-step turns
/// taken. Each turn's board transition is proven by the committed D1 AIR
/// (`new == automaton_step(old)`); the boards themselves are never posted.
#[derive(Clone, Debug)]
pub struct AutomataflMatch {
    /// The starting board (the match's genesis position).
    pub start: Board,
    /// How many automaton-step turns the match played.
    pub turns: usize,
}

impl AutomataflMatch {
    /// The played board sequence: `start`, then each successive `automaton_step`.
    pub fn boards(&self) -> Vec<Board> {
        let mut bs = Vec::with_capacity(self.turns + 1);
        bs.push(self.start.clone());
        for i in 0..self.turns {
            bs.push(automaton_step(&bs[i]));
        }
        bs
    }

    /// Lower the played match to the foldable leaves: one committed **D1 Custom leaf** per
    /// turn, each proving `boards[i+1] == automaton_step(boards[i])`.
    pub fn leaves(&self) -> Result<Vec<LeafBundle>, MatchError> {
        if self.turns == 0 {
            return Err(MatchError::Empty);
        }
        let boards = self.boards();
        let mut out = Vec::with_capacity(self.turns);
        for (i, old) in boards.iter().take(self.turns).enumerate() {
            let b = build_d1_honest(old);
            if !b.air_accepts() {
                return Err(MatchError::D1Refused(i));
            }
            let rows = 2usize;
            out.push(LeafBundle {
                program: b.cellprogram(),
                witness_values: b.trace_witness(rows),
                num_rows: rows,
                public_inputs: b.pis.clone(),
            });
        }
        Ok(out)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// (2) The fold: a played match → ONE succinct proof.
// ═══════════════════════════════════════════════════════════════════════════════

/// Why a match did not produce a shippable proof.
#[derive(Clone, Debug)]
pub enum ProveError {
    /// The played match did not lower to foldable leaves.
    Match(MatchError),
    /// The deployed recursive fold refused the chain (a forged match has no satisfying leaf,
    /// so its turn is UNSAT and there is no root).
    Fold(String),
    /// The fold produced an artifact the light client itself does not accept — a prover bug.
    /// (Self-attestation before shipping: we never hand the board a proof we cannot verify.)
    SelfAttest(LightClientError),
}

impl fmt::Display for ProveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProveError::Match(e) => write!(f, "the match did not lower to leaves: {e}"),
            ProveError::Fold(e) => write!(f, "the recursive fold refused the match: {e}"),
            ProveError::SelfAttest(e) => {
                write!(
                    f,
                    "the folded artifact failed prover-side self-attestation: {e}"
                )
            }
        }
    }
}

impl std::error::Error for ProveError {}

/// **THE FOLDED MATCH** — one succinct `WholeChainProof` (as its wire envelope) plus the
/// publics the whole-history light client attests. This is the ENTIRE object that leaves the
/// player: no hand, no cards, no boards, no moves.
#[derive(Clone, Debug)]
pub struct MatchProof {
    /// Which game the match was played in.
    pub game: Game,
    /// The succinct whole-history proof envelope (`WholeChainProof::to_bytes()`) — what the
    /// board verifies in O(1) and stores in place of the moves.
    pub proof_bytes: Vec<u8>,
    /// The publics the light client attests: the genesis anchor, the final anchor (the WIN),
    /// the ordered-history digest, and the turn count.
    pub attested: AttestedHistory,
    /// The root-circuit VK fingerprint of THIS fold. A setup party mints the board's trust
    /// anchor from its own honest fold; a submitter's claimed fingerprint is never trusted (the
    /// board compares against its pinned [`ProofAnchor::vk`]).
    pub vk: RecursionVk,
}

impl MatchProof {
    /// The number of turns the attested history folds — the leaderboard's rank key.
    pub fn turns(&self) -> usize {
        self.attested.num_turns
    }
}

/// **PROVE a played match**: fold its leaves through the game's committed Phase-3 fold
/// (`prove_turn_chain_recursive`) into ONE `WholeChainProof`, then SELF-ATTEST it with the real
/// light client before shipping. SLOW (minutes-to-hours) — this is the step
/// [`ProvingService`] runs in the background.
///
/// The identical path for both games: the leaves differ (a Poseidon2 membership leaf; a D1
/// board-transition leaf), the fold does not.
pub fn prove_match(game: Game, leaves: &[LeafBundle]) -> Result<MatchProof, ProveError> {
    if leaves.is_empty() {
        return Err(ProveError::Match(MatchError::Empty));
    }
    let whole = fold_match(leaves).map_err(ProveError::Fold)?;
    let vk = whole.root_vk_fingerprint();
    let proof_bytes = whole.to_bytes();
    // Prover-side self-attestation through the SAME verifier the board runs (over the SAME
    // wire envelope the board will receive).
    let attested = verify_history_bytes(&proof_bytes, &vk).map_err(ProveError::SelfAttest)?;
    Ok(MatchProof {
        game,
        proof_bytes,
        attested,
        vk,
    })
}

/// Fold a played multiway-tug match (play → prove). SLOW.
pub fn prove_tug_match(m: &TugMatch) -> Result<MatchProof, ProveError> {
    let leaves = m.leaves().map_err(ProveError::Match)?;
    prove_match(Game::MultiwayTug, &leaves)
}

/// **PROVE THE TERMINAL WIN OVER THE REAL WORLDCELL CELL.** The board layer ADOPTING the
/// real-cell fold bridge: snapshot the game's OWN committed cell
/// (`spween_dregg::WorldCell::cell_snapshot`) after its real `score` turn and fold the win over
/// it (`dregg_multiway_tug::fold::fold_win_over_cell`). The ranked proof's win root is welded to
/// the cell whose committed `new8` the deployed win implication (`winner==p ⇒ charm_p>=11 OR
/// guilds_p>=4`, `WriteOnce(winner)`) already gated at `score` admission — NOT the `pk[0]=7`,
/// balance-1000 fixture the free `[charm, winner]` literal path folded over.
///
/// This is the closure of the board's win mannequin: `prove_tug_match` (above) still folds the
/// free `win_leaf` literal, which carries no cell state; this path folds over the real cell.
/// SLOW (the deployed recursion fold).
pub fn prove_tug_win_over_cell(
    game: &dregg_multiway_tug::game::MultiwayTug,
    charm: u64,
    winner: u64,
) -> Result<MatchProof, ProveError> {
    let cell = game
        .world()
        .cell_snapshot()
        .ok_or_else(|| ProveError::Fold("the world-cell has no committed state".to_string()))?;
    let whole = dregg_multiway_tug::fold::fold_win_over_cell(&cell, charm, winner)
        .map_err(ProveError::Fold)?;
    let vk = whole.root_vk_fingerprint();
    let proof_bytes = whole.to_bytes();
    let attested = verify_history_bytes(&proof_bytes, &vk).map_err(ProveError::SelfAttest)?;
    Ok(MatchProof {
        game: Game::MultiwayTug,
        proof_bytes,
        attested,
        vk,
    })
}

/// Fold a played automatafl match (play → prove). SLOW.
pub fn prove_automatafl_match(m: &AutomataflMatch) -> Result<MatchProof, ProveError> {
    let leaves = m.leaves().map_err(ProveError::Match)?;
    prove_match(Game::Automatafl, &leaves)
}

// ═══════════════════════════════════════════════════════════════════════════════
// (3) The proof-carrying board.
// ═══════════════════════════════════════════════════════════════════════════════

/// **Pin a game's [`ProofAnchor`] from a canonical WON match's fold**: the light-client VK, the
/// genesis anchor its runs start from, and the final anchor that encodes the **WIN**.
///
/// This is CONFIG the board operator holds — exactly like a distributed SNARK VK. It is never
/// read off a submitted proof (which the submitter controls): a submission is accepted only if
/// ITS attested roots equal these pinned ones, so a submitter cannot pick their own win.
pub fn match_anchor(p: &MatchProof) -> ProofAnchor {
    ProofAnchor::new(p.vk, p.attested.genesis_root, p.attested.final_root)
}

/// Why a submission to the game board failed.
#[derive(Clone, Debug)]
pub enum SubmitError {
    /// No board is open for that game.
    NoBoard(Game),
    /// The proof-carrying board REFUSED the proof (the O(1) light-client tooth, the genesis /
    /// WIN anchor binding, or the claimed-turns binding).
    Refused(RejectReason),
    /// The background fold never produced a proof to submit (the async path's own failure — a
    /// forged/unsatisfiable match, or a prover error). Nothing reached the board.
    Proving(String),
}

impl fmt::Display for SubmitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SubmitError::NoBoard(g) => write!(f, "no proof-carrying board is open for {g}"),
            SubmitError::Refused(r) => write!(f, "the board refused the proof: {r}"),
            SubmitError::Proving(e) => write!(f, "the match never folded to a proof: {e}"),
        }
    }
}

impl std::error::Error for SubmitError {}

/// **THE GAMES' PROOF-CARRYING LEADERBOARD** — one `ugc-dregg` [`Registry`] hosting a board
/// universe per game, each pinned to that game's [`ProofAnchor`]. A submission is a
/// [`ProofCompletion`] (a proof, never moves); the board verifies it in O(1)
/// (`verify_history_bytes`) and ranks it; the accepted [`Entry`] stores NO moves.
#[derive(Default)]
pub struct GameBoard {
    registry: Registry,
    universes: BTreeMap<Game, UniverseId>,
}

impl GameBoard {
    /// An empty board (no games open yet).
    pub fn new() -> GameBoard {
        GameBoard::default()
    }

    /// **OPEN a game's board**: publish its universe against the pinned [`ProofAnchor`] (the
    /// VK + genesis + WIN root). Returns the board universe's content address.
    pub fn open(&mut self, game: Game, anchor: ProofAnchor) -> UniverseId {
        let u = Universe::authored(
            game.title(),
            "dregg-game-board",
            &game.scene(),
            WinCondition::ended(),
        )
        .expect("the game board's universe scene is a valid deployable world")
        .with_proof_anchor(anchor);
        let id = self.registry.publish(u);
        self.universes.insert(game, id);
        id
    }

    /// The board universe id for a game, if open.
    pub fn universe(&self, game: Game) -> Option<UniverseId> {
        self.universes.get(&game).copied()
    }

    /// **SUBMIT a folded match** to the game's proof-carrying board. The board verifies the
    /// proof in **O(1)** — re-witnessing nothing, replaying no move, and never seeing the hand
    /// or the boards — and, only on success, RANKS it. A forged proof, a proof from another
    /// game/universe, or a lied turn count is REFUSED and nothing is added.
    pub fn submit(
        &mut self,
        game: Game,
        player: &str,
        proof: &MatchProof,
    ) -> Result<Accepted, SubmitError> {
        self.submit_bytes(game, player, proof.proof_bytes.clone(), proof.turns())
    }

    /// Submit a raw proof envelope + claimed turns (the wire shape: what actually crosses the
    /// network from a player's prover to the board).
    pub fn submit_bytes(
        &mut self,
        game: Game,
        player: &str,
        proof_bytes: Vec<u8>,
        claimed_turns: usize,
    ) -> Result<Accepted, SubmitError> {
        let universe = self.universe(game).ok_or(SubmitError::NoBoard(game))?;
        self.registry
            .submit_proof(ProofCompletion {
                universe,
                player: player.to_string(),
                proof_bytes,
                claimed_turns,
            })
            .map_err(SubmitError::Refused)
    }

    /// The game's leaderboard — accepted entries ranked by turns (lower first). Every entry
    /// here provably reached the pinned WIN anchor.
    pub fn leaderboard(&self, game: Game) -> Vec<&Entry> {
        match self.universe(game) {
            Some(id) => self.registry.leaderboard(id),
            None => Vec::new(),
        }
    }

    /// **THE PRIVATE-STRATEGY PROPERTY**: every ranked entry on this game's board is
    /// proof-backed and stores NO moves. `true` for an empty board (vacuously) — assert it
    /// alongside a non-empty leaderboard.
    pub fn stores_no_moves(&self, game: Game) -> bool {
        self.leaderboard(game)
            .iter()
            .all(|e| e.is_proof_backed() && !e.has_moves() && e.playthrough().is_none())
    }

    /// **Independently re-verify** a ranked entry — re-running the O(1) light client on the
    /// stored proof against the pinned anchor. Never a replay: the moves were never posted.
    pub fn reverify(&self, game: Game, completion_id: &[u8; 32]) -> Result<usize, SubmitError> {
        let universe = self.universe(game).ok_or(SubmitError::NoBoard(game))?;
        self.registry
            .reverify_entry(universe, completion_id)
            .map_err(SubmitError::Refused)
    }

    /// The underlying `ugc-dregg` registry (for callers that want the full board API).
    pub fn registry(&self) -> &Registry {
        &self.registry
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// (4) The ASYNC shape: play (fast) → prove (slow, background) → submit (the proof).
// ═══════════════════════════════════════════════════════════════════════════════

/// A queued proving job's handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JobId(pub u64);

/// Where a proving job is. The player's client polls this; the board is not involved until
/// [`JobStatus::Ready`].
#[derive(Clone, Debug)]
pub enum JobStatus {
    /// Enqueued, not yet picked up.
    Queued,
    /// The worker is folding the match (the slow step).
    Proving,
    /// The fold is done and self-attested — this proof can be submitted to the board.
    Ready(Box<MatchProof>),
    /// The fold refused the match (a forged/unsatisfiable chain) or the prover errored.
    Failed(String),
    /// No such job.
    Unknown,
}

impl JobStatus {
    /// The finished proof, if this job is [`JobStatus::Ready`].
    pub fn ready(&self) -> Option<&MatchProof> {
        match self {
            JobStatus::Ready(p) => Some(p),
            _ => None,
        }
    }
    /// Whether the job has settled (ready or failed).
    pub fn is_settled(&self) -> bool {
        matches!(self, JobStatus::Ready(_) | JobStatus::Failed(_))
    }
}

/// The proving backend a [`ProvingService`] runs: a played match's leaves → a shippable
/// [`MatchProof`]. The production backend is [`stark_prover`] (the deployed recursive fold).
pub type Prover = Arc<dyn Fn(Game, Vec<LeafBundle>) -> Result<MatchProof, String> + Send + Sync>;

/// The REAL proving backend — the deployed recursive fold ([`prove_match`]). SLOW.
pub fn stark_prover() -> Prover {
    Arc::new(|game, leaves| prove_match(game, &leaves).map_err(|e| e.to_string()))
}

struct Job {
    id: JobId,
    game: Game,
    leaves: Vec<LeafBundle>,
}

/// **THE ASYNC PROVING SERVICE.** Play is interactive-fast; the fold is minutes-to-hours. A
/// finished match is ENQUEUED here and proven on a background worker thread; the player polls
/// [`ProvingService::status`] (or blocks on [`ProvingService::wait`]) and submits the proof to
/// the [`GameBoard`] when it is ready. The board's own work stays O(1) and it never needs the
/// moves — so nothing in the pipeline ever has to hold, transmit, or store them.
pub struct ProvingService {
    tx: Option<Sender<Job>>,
    state: Arc<(Mutex<BTreeMap<u64, JobStatus>>, Condvar)>,
    next: AtomicU64,
    worker: Option<JoinHandle<()>>,
}

impl ProvingService {
    /// Spawn the service with a proving backend (in production: [`stark_prover`]).
    pub fn spawn(prover: Prover) -> ProvingService {
        let (tx, rx) = channel::<Job>();
        let state: Arc<(Mutex<BTreeMap<u64, JobStatus>>, Condvar)> =
            Arc::new((Mutex::new(BTreeMap::new()), Condvar::new()));
        let worker_state = Arc::clone(&state);
        let worker = std::thread::Builder::new()
            .name("game-board-prover".into())
            .spawn(move || {
                for job in rx {
                    set_status(&worker_state, job.id, JobStatus::Proving);
                    let outcome = match (prover)(job.game, job.leaves) {
                        Ok(p) => JobStatus::Ready(Box::new(p)),
                        Err(e) => JobStatus::Failed(e),
                    };
                    set_status(&worker_state, job.id, outcome);
                }
            })
            .expect("the proving worker thread spawns");
        ProvingService {
            tx: Some(tx),
            state,
            next: AtomicU64::new(1),
            worker: Some(worker),
        }
    }

    /// **ENQUEUE a played match** for proving. Returns immediately with a [`JobId`] — the play
    /// is over; the fold happens in the background.
    pub fn enqueue(&self, game: Game, leaves: Vec<LeafBundle>) -> JobId {
        let id = JobId(self.next.fetch_add(1, Ordering::Relaxed));
        set_status(&self.state, id, JobStatus::Queued);
        self.tx
            .as_ref()
            .expect("service is running")
            .send(Job { id, game, leaves })
            .expect("the proving worker is alive");
        id
    }

    /// Poll a job.
    pub fn status(&self, id: JobId) -> JobStatus {
        let (m, _) = &*self.state;
        m.lock()
            .expect("job map")
            .get(&id.0)
            .cloned()
            .unwrap_or(JobStatus::Unknown)
    }

    /// Block until the job settles, then hand back the proof (or the fold's refusal).
    pub fn wait(&self, id: JobId) -> Result<MatchProof, String> {
        let (m, cv) = &*self.state;
        let mut guard = m.lock().expect("job map");
        loop {
            match guard.get(&id.0) {
                Some(JobStatus::Ready(p)) => return Ok((**p).clone()),
                Some(JobStatus::Failed(e)) => return Err(e.clone()),
                Some(_) => {}
                None => return Err(format!("unknown job {}", id.0)),
            }
            guard = cv.wait(guard).expect("job condvar");
        }
    }

    /// **PROVE-THEN-SUBMIT**, the whole async tail in one call: wait for the fold, then hand
    /// the proof (never the moves) to the game's proof-carrying board, which verifies it in
    /// O(1) and ranks it.
    pub fn submit_when_ready(
        &self,
        board: &mut GameBoard,
        game: Game,
        player: &str,
        id: JobId,
    ) -> Result<Accepted, SubmitError> {
        let proof = self.wait(id).map_err(SubmitError::Proving)?;
        board.submit(game, player, &proof)
    }
}

fn set_status(state: &Arc<(Mutex<BTreeMap<u64, JobStatus>>, Condvar)>, id: JobId, s: JobStatus) {
    let (m, cv) = &**state;
    m.lock().expect("job map").insert(id.0, s);
    cv.notify_all();
}

impl Drop for ProvingService {
    fn drop(&mut self) {
        // Close the queue so the worker's `for job in rx` loop ends, then join it.
        drop(self.tx.take());
        if let Some(w) = self.worker.take() {
            let _ = w.join();
        }
    }
}
