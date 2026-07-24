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

use dregg_automatafl::reference::{Board, Move, automaton_step};
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
    /// An automatafl step (Leg A) trace did not satisfy the PROVEN Lean step descriptor
    /// (`automataflStepDescN`) — the fail-closed witness-gen canary refused it before any proving.
    D1Refused(usize),
    /// A two-leg round's RESOLVE leg (Leg R, `old → mid`) did not satisfy the PROVEN Lean
    /// resolve descriptor — an illegal / unresolvable move pair, refused before any proving.
    ResolveRefused(usize),
    /// A CONFLICT round's Leg C (`roundStep`'s `.again` branch) did not satisfy the PROVEN Lean
    /// `automataflLegCDescN` — a non-clashing pair (UNSAT: `cSurv` is pinned to 0), a submission
    /// naming an accumulated mark (the `marksIn`-legality pin), or a mis-fill — refused before any
    /// proving (the fail-closed witness-gen canary).
    ConflictRefused(usize),
    /// The board size has no emitted Lean descriptor for one of the two legs (the n = 5 case).
    /// BLOCKED, not faked: a two-leg round cannot be attested at a size the Lean AIR is not
    /// emitted for.
    NoDescriptor(usize, String),
    /// The match has no turns — there is nothing to fold.
    Empty,
}

impl fmt::Display for MatchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MatchError::NotInHand(c) => write!(f, "card {c} is not under the current hand root"),
            MatchError::Lowering(e) => write!(f, "membership lowering refused the play: {e}"),
            MatchError::D1Refused(i) => write!(f, "automatafl step {i}: the D1 AIR self-rejected"),
            MatchError::ResolveRefused(i) => write!(
                f,
                "automatafl round {i}: the RESOLVE leg did not satisfy the Lean resolve descriptor"
            ),
            MatchError::ConflictRefused(i) => write!(
                f,
                "automatafl conflict round {i}: Leg C did not satisfy the Lean automataflLegCDescN \
                 (non-clash, a submission on an accumulated mark, or a mis-fill)"
            ),
            MatchError::NoDescriptor(n, which) => write!(
                f,
                "automatafl n={n}: no emitted Lean {which} descriptor — the two-leg round is \
                 BLOCKED at this board size, not faked"
            ),
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
        descriptor_state_leaf: None,
    }
}

/// Overwrite a descriptor leaf's FREE 16-felt `[old8 ‖ new8]` door with the rotated roots of the
/// leg the fold will mint for it. The door lanes carry no `pi_binding` (the AIR does not constrain
/// them — the FOLD does), so this changes nothing the descriptor proves and everything the
/// deployed state tooth checks: without it the leaf claims a transition about a cell the leg never
/// touched, and the `connect` is UNSAT.
fn set_state_door(pis: &mut [BabyBear], old8: [BabyBear; 8], new8: [BabyBear; 8]) {
    debug_assert!(
        pis.len() >= 16,
        "a state-binding leaf publishes the 16-felt door"
    );
    pis[..8].copy_from_slice(&old8);
    pis[8..16].copy_from_slice(&new8);
}

/// A **PLAYED automatafl match**: the starting board and the number of automaton-step turns
/// taken. Each turn's board transition is proven by the committed D1 AIR
/// (`new == automaton_step(old)`); the boards themselves are never posted.
#[derive(Clone, Debug)]
pub struct AutomataflMatch {
    /// The starting board (the match's genesis position).
    pub start: Board,
    /// How many automaton-step turns the match played. Read ONLY when `rounds` is empty (the
    /// legacy automaton-only shape — see [`AutomataflMatch::leaves`]).
    pub turns: usize,
    /// **THE PLAYED ROUNDS** — the two seats' submitted moves, in order. A non-empty `rounds`
    /// selects the TWO-LEG fold (`resolve` then `step` per round, chained by the board window);
    /// an empty one keeps the legacy automaton-only chain, which attests no move at all.
    pub rounds: Vec<(Move, Move)>,
}

impl AutomataflMatch {
    /// A played match from its rounds — the shape the two-leg fold attests.
    pub fn played(start: Board, rounds: Vec<(Move, Move)>) -> AutomataflMatch {
        AutomataflMatch {
            start,
            turns: 0,
            rounds,
        }
    }

    /// The legacy automaton-only match (no player moves, no resolve leg).
    pub fn automaton_only(start: Board, turns: usize) -> AutomataflMatch {
        AutomataflMatch {
            start,
            turns,
            rounds: Vec::new(),
        }
    }

    /// **THE TWO-LEG ROUND LEAVES** — for each played round, the RESOLVE leaf (Leg R,
    /// `old → mid`, adjudicating the two submitted moves through the PROVEN Lean
    /// `automataflResolveDescN n`) then the STEP leaf (Leg A, `mid → new`, the automaton through
    /// `automataflStepDescN n`), both carrying a BOARD WINDOW so the fold chains them.
    ///
    /// ## What the window makes true (and what it does not)
    ///
    /// Every leaf declares `IN = pack(board it consumed) ‖ automaton` and
    /// `OUT = pack(board it produced) ‖ automaton`. The fold `connect`s `left.OUT == right.IN` at
    /// every aggregation node, so:
    ///
    /// * `R_i.OUT == A_i.IN` is exactly `hseamPack ∧ hseamAutoX ∧ hseamAutoY` — the hypotheses
    ///   `AutomataflTurnCapstone.turn_sat_imp_roundStep_pi` takes, so the round's `new` board IS
    ///   `AutomataflRules.roundStep`'s outcome board for the decoded moves;
    /// * `A_i.OUT == R_{i+1}.IN` is the inter-round carry — the boards form ONE trajectory, not K
    ///   independent transitions;
    /// * the root exposes `[first.IN ‖ last.OUT]` — the genesis and final positions, decodable in
    ///   the clear (the pack is injective).
    ///
    /// NOT attested by this: WHOSE moves these are. The resolve descriptor's move columns are free
    /// witness (`moveDecodeN` hard-codes `who = 0`), so a folded round says "the transition is a
    /// legal resolution of SOME valid move pair, carried into the automaton step" — the sealed-move
    /// reveal leg (Leg S) is what would bind them to the two seats, and it is not folded here.
    /// Nor are the spec-side `hfresh` / `hres` hypotheses discharged.
    ///
    /// The leaf's `[old8 ‖ new8]` door is filled with the REAL rotated roots of the leg the fold
    /// will mint for that chain position ([`dregg_multiway_tug::fold::fixture_rotated_roots`]), so
    /// the deployed state tooth holds; a placeholder door would be UNSAT.
    pub fn round_leaves(&self) -> Result<Vec<LeafBundle>, MatchError> {
        use dregg_automatafl::resolve_witness::{
            automatafl_resolve_trace, resolve_board_window, resolve_descriptor_ident,
            resolve_trace_accepts,
        };
        use dregg_automatafl::witness::{
            automatafl_step_trace, step_board_window, step_descriptor_name, step_trace_accepts,
        };
        use dregg_circuit::descriptor_by_name::descriptor_by_name;
        use dregg_circuit_prove::joint_turn_aggregation::DescriptorStateLeafSource;
        use dregg_multiway_tug::fold::fixture_rotated_roots;

        if self.rounds.is_empty() {
            return Err(MatchError::Empty);
        }
        let n = self.start.n;
        let rdesc = descriptor_by_name(resolve_descriptor_ident(n))
            .ok_or_else(|| MatchError::NoDescriptor(n, "resolve".to_string()))?;
        let sdesc = descriptor_by_name(&step_descriptor_name(n))
            .ok_or_else(|| MatchError::NoDescriptor(n, "step".to_string()))?;
        let rwin = resolve_board_window(n, &rdesc)
            .map_err(|e| MatchError::NoDescriptor(n, format!("resolve window: {e}")))?;
        let awin = step_board_window(n, &sdesc)
            .map_err(|e| MatchError::NoDescriptor(n, format!("step window: {e}")))?;
        let layout = dregg_automatafl::resolve_layout::ResolveLayout::new(n);

        let rows = 2usize; // >= 2 so the `when_transition` gates are exercised.
        let mut out: Vec<LeafBundle> = Vec::with_capacity(2 * self.rounds.len());
        let mut board = self.start.clone();

        for (i, (ma, mb)) in self.rounds.iter().enumerate() {
            // ---- Leg R: adjudicate the two moves, old -> mid. ----
            let mut rt = automatafl_resolve_trace(&board, &[*ma, *mb], &rdesc)
                .map_err(|e| MatchError::Lowering(format!("round {i} resolve witness-gen: {e}")))?;
            let (r_old8, r_new8) = fixture_rotated_roots(out.len() as u64);
            set_state_door(&mut rt.public_inputs, r_old8, r_new8);
            if !resolve_trace_accepts(&rdesc, &rt) {
                return Err(MatchError::ResolveRefused(i));
            }
            let mid = rt.mid_board(&layout);
            out.push(LeafBundle::descriptor_backed(
                rt.public_inputs.clone(),
                rows,
                DescriptorStateLeafSource {
                    descriptor: rdesc.clone(),
                    base_trace: rt.base_trace(rows),
                    board_window: Some(rwin.clone()),
                },
            ));

            // ---- Leg A: step the automaton, mid -> new. ----
            let mut st = automatafl_step_trace(&mid, &sdesc)
                .map_err(|e| MatchError::Lowering(format!("round {i} step witness-gen: {e}")))?;
            let (a_old8, a_new8) = fixture_rotated_roots(out.len() as u64);
            set_state_door(&mut st.public_inputs, a_old8, a_new8);
            if !step_trace_accepts(&sdesc, &st) {
                return Err(MatchError::D1Refused(i));
            }
            out.push(LeafBundle::descriptor_backed(
                st.public_inputs.clone(),
                rows,
                DescriptorStateLeafSource {
                    descriptor: sdesc.clone(),
                    base_trace: st.base_trace(rows),
                    board_window: Some(awin.clone()),
                },
            ));

            board = automaton_step(&mid);
        }
        Ok(out)
    }

    /// The played board sequence a two-leg match walks: `start`, then each round's
    /// `automaton_step(resolve(board, moves))`.
    pub fn round_boards(&self) -> Vec<Board> {
        let mut bs = Vec::with_capacity(self.rounds.len() + 1);
        let mut b = self.start.clone();
        bs.push(b.clone());
        for (ma, mb) in &self.rounds {
            b = automaton_step(&dregg_automatafl::reference::resolve_mid(&b, &[*ma, *mb]));
            bs.push(b.clone());
        }
        bs
    }
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
    ///
    /// **The leaf proves the transition through the PROVEN Lean-emitted descriptor**
    /// (`automataflStepDescN {n}`, refined against `automatonStep`) — house-law #1: the AIR is
    /// authored in Lean, never in Rust. The trusted witness generator
    /// ([`dregg_automatafl::witness::automatafl_step_trace`]) SOLVES the descriptor's own gates to
    /// fill its trace, the leaf's public inputs ARE the descriptor's PIs
    /// (`old8‖new8 ‖ packed_old ‖ packed_new ‖ ax ‖ ay ‖ nax ‖ nay`), and the fold mints the
    /// sub-proof leaf via `prove_custom_leaf_descriptor_with_state_commitment` (see
    /// [`DescriptorStateLeafSource`] / [`LeafBundle::descriptor_backed`]). The hand-authored Rust AIR
    /// is DELETED — the descriptor is the sole authority.
    ///
    /// Emitted sizes are `n ∈ {2, 11}`; a board size with NO emitted Lean descriptor (the former
    /// `n = 5` TEST size) is BLOCKED-not-faked ([`MatchError::NoDescriptor`]) — there is no Rust-AIR
    /// fallback, so a size the Lean AIR is not emitted for cannot be attested.
    pub fn leaves(&self) -> Result<Vec<LeafBundle>, MatchError> {
        use dregg_automatafl::witness::{
            automatafl_step_trace, step_descriptor_name, step_trace_accepts,
        };
        use dregg_circuit::descriptor_by_name::descriptor_by_name;
        use dregg_circuit_prove::joint_turn_aggregation::DescriptorStateLeafSource;

        // A match with PLAYED ROUNDS folds the two-leg chain (resolve ∘ step, board-window
        // chained). The automaton-only path below is what remains when no moves were submitted —
        // it attests K INDEPENDENT automaton steps and no move at all.
        if !self.rounds.is_empty() {
            return self.round_leaves();
        }
        if self.turns == 0 {
            return Err(MatchError::Empty);
        }
        let boards = self.boards();
        let mut out = Vec::with_capacity(self.turns);
        for (i, old) in boards.iter().take(self.turns).enumerate() {
            let rows = 2usize;
            // The PROVEN Lean descriptor for this board size (blocked-not-faked at an unemitted size).
            let desc = descriptor_by_name(&step_descriptor_name(old.n))
                .ok_or_else(|| MatchError::NoDescriptor(old.n, "step".to_string()))?;
            let tr = automatafl_step_trace(old, &desc).map_err(|e| {
                MatchError::Lowering(format!(
                    "automatafl step-{i} witness-gen (n={}): {e}",
                    old.n
                ))
            })?;
            // Fail-closed canary: the generated trace must satisfy the Lean descriptor (the real
            // Ir2Air row-local evaluator) before it is folded — a mis-fill is refused here, never
            // handed to the prover. This is the gate the deleted Rust-AIR `air_accepts` used to be.
            if !step_trace_accepts(&desc, &tr) {
                return Err(MatchError::D1Refused(i));
            }
            let base_trace = tr.base_trace(rows);
            out.push(LeafBundle::descriptor_backed(
                tr.public_inputs,
                rows,
                DescriptorStateLeafSource {
                    descriptor: desc,
                    base_trace,
                    // The automaton-only chain declares NO board window: nothing connects turn i's
                    // board to turn i+1's. That is the gap; the two-leg `round_leaves` path closes it.
                    board_window: None,
                },
            ));
        }
        Ok(out)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// (1b) A MULTI-ROUND automatafl turn: the CONFLICT BRAID (a Leg C chain) + the clean round.
// ═══════════════════════════════════════════════════════════════════════════════

/// **A MULTI-ROUND automatafl turn** — `k` CONFLICT rounds (each a `roundStep` `.again` re-entry: a
/// fork/collide marks the clashed coordinate, FREEZES the board, and re-enters) then the
/// terminating CLEAN round (the resolve that settles the turn).
///
/// ## The conflict braid folds as a UNIFORM 32-lane RoundState chain (fully wired)
///
/// Every conflict round lowers to ONE Leg C leaf (`automataflLegCDescN 11`, HASH-FREE, ZERO
/// lookups) that declares the whole 32-lane RoundState window
/// `[board(9) ‖ marks(9) ‖ locked(10) ‖ waiting(2) ‖ auto(2)]`
/// ([`leg_c_roundstate_window_n11`](dregg_circuit::effect_vm::custom_state_binding::leg_c_roundstate_window_n11)).
/// The ONLY cross-leaf rule is `C_i.OUT == C_{i+1}.IN`, which the DEPLOYED `aggregate_tree`
/// connects lane-by-lane — the merge auto-derives the width from the exposed shape
/// (`SEG_WIDTH + 2·32 = 89`), so a same-width Leg C chain folds through the existing
/// [`prove_match`] path with NO M7-specific prover code. The chain accumulates the marks overlay:
/// `marksIn_0 = ∅` and `marksIn_{i+1}` is the marks `C_i` produced (`marksOut = marksIn ∨ clash`,
/// read back from the Leg C trace itself, not re-derived). Because `pack` is injective and the
/// seam is a lane-for-lane `connect`, a DROPPED round (a downstream `marksIn` the upstream never
/// produced) or a SUBSTITUTED round (a forged `marksOut`) is a broken seam — a `WitnessConflict`,
/// a witness that does not exist, not a soft constraint.
///
/// ## The `C_last → R` handoff now connects `board ‖ marks` (the marks half is CLOSED at mint)
///
/// The terminating clean round consumes the ACCUMULATED marks: [`MultiRoundTurn::clean_leaves`]
/// mints the marks-aware **Leg RM** (`automataflResolveMarksDescN 11` — now EMITTED as
/// `automatafl-resolve-marks-n11.json`, filled by
/// [`dregg_automatafl::resolve_marks_witness::automatafl_resolve_marks_trace`]) then the automaton
/// **Leg A** step. Leg RM declares the 20-lane `[board(9) ‖ marks(9) ‖ auto(2)]` window
/// ([`resolve_marks_board_window`](dregg_automatafl::resolve_marks_witness::resolve_marks_board_window)),
/// whose `board ‖ marks` prefix (18 lanes) is laid out identically to the conflict rounds' RoundState
/// window. So the handoff primitive
/// [`board_window_clean_handoff_connects`](dregg_circuit_prove) welds the FULL 18-lane
/// `board ‖ marks` (not board-only): `marksIn` on the clean side is read back from the conflict
/// chain's `marksOut`, and a dropped / substituted conflict round makes it disagree — a broken seam.
/// Leg RM ALSO re-checks that the terminating move avoids an accumulated mark
/// (`AutomataflResolveMarksCapstone.resolveMarksMoveLegal`, M6, PROVEN in Lean — the legality NOR
/// pin), so the move-vs-marks legality is attested at the terminating move, not only at the conflict
/// rounds.
///
/// ## What is STILL a residual (welding to ONE verifying root), surfaced not faked
///
/// 1. **The clean sub-chain is not uniform-width, so it cannot fold through the deployed
///    `aggregate_tree`.** Leg RM is 20-lane `[board ‖ marks ‖ auto]`; Leg A (the automaton step,
///    `automataflStepDescN 11`) publishes NO marks PIs, so its window is the 11-lane `[board ‖ auto]`
///    — the step descriptor has no marks columns to expose. `aggregate_tree` /
///    `merge_two_segment_proofs` refuse a mixed 20/11 chain, and a nested clean-handoff sub-root
///    `[RM.IN(20) ‖ A.OUT(11)]` is not the uniform `SEG + 2W` shape [`exposed_board_window`] reads —
///    so the top `merge_clean_handoff_segment_proofs` refuses it. Folding the automaton step into the
///    marks-carrying clean sub-chain needs a marks-carrying step descriptor emitted in Lean (or the
///    clean round modeled as ONE resolve+step leaf) — Lean-authored AIR, not Rust.
/// 2. **No `WholeChainProof` assembly exists for the clean-handoff root.**
///    [`fold_clean_handoff_root`](dregg_circuit_prove) produces the mixed root
///    `RecursionOutput`, and the light-client verifier ALREADY accepts a mixed-width board window
///    (`verify_turn_chain_recursive_from_parts_with_board_window` tooth (5)) plus
///    [`board_window_of_chain_with_clean_handoff`] computes the carried window — but the prover-side
///    glue that assembles the root + the clean-handoff-shaped segment host mirror + the binding
///    descriptor proof into a verifiable `WholeChainProof` is not built (the uniform `fold_match`
///    path is the only assembler today). This is `dregg-circuit-prove` systems work, orthogonal to
///    residual (1).
///
/// So [`MultiRoundTurn::conflict_leaves`] and the marks-carrying [`MultiRoundTurn::clean_leaves`] are
/// foldable, self-contained, mint-coherent artifacts (the `board ‖ marks` handoff and the
/// terminating marks-legality now hold at mint level); welding the WHOLE turn — conflict braid ∘ Leg
/// RM ∘ Leg A — into ONE verifying root is BLOCKED on residuals (1) and (2).
#[derive(Clone, Debug)]
pub struct MultiRoundTurn {
    /// The turn-start board — FROZEN across the whole conflict braid.
    pub start: Board,
    /// The `k` conflict rounds' submissions, in re-entry order. Each MUST clash (fork/collide); a
    /// non-clashing pair is UNSAT as a Leg C (`cSurv` pinned to 0). Round `i+1` is entered with the
    /// marks round `i` produced, so a submission naming an accumulated mark is refused.
    pub conflict_subs: Vec<[Move; 2]>,
    /// The terminating CLEAN round's submissions (resolve then step). `None` folds the conflict
    /// braid alone (the self-contained uniform-32 segment).
    pub clean_subs: Option<[Move; 2]>,
}

impl MultiRoundTurn {
    /// A turn from its conflict rounds and terminating clean round.
    pub fn new(
        start: Board,
        conflict_subs: Vec<[Move; 2]>,
        clean_subs: [Move; 2],
    ) -> MultiRoundTurn {
        MultiRoundTurn {
            start,
            conflict_subs,
            clean_subs: Some(clean_subs),
        }
    }

    /// A turn's conflict braid alone (no terminating clean round) — the foldable uniform-32
    /// segment.
    pub fn conflict_only(start: Board, conflict_subs: Vec<[Move; 2]>) -> MultiRoundTurn {
        MultiRoundTurn {
            start,
            conflict_subs,
            clean_subs: None,
        }
    }

    /// **THE CONFLICT-BRAID LEAVES** — one Leg C leaf per conflict round, chained on the RoundState
    /// seam. Round `i` is filled by [`dregg_automatafl::legc_witness::automatafl_legc_trace`] over
    /// `RoundStateIn { board: start (frozen), marks: marksIn_i }`, verified against the PROVEN
    /// `automataflLegCDescN 11` by the fail-closed canary
    /// [`legc_trace_accepts`](dregg_automatafl::legc_witness::legc_trace_accepts) BEFORE it is
    /// folded; `marksIn_{i+1}` is the `marksOut` the round produced (read back from the trace).
    /// Every leaf declares the 32-lane RoundState window so the fold connects `C_i.OUT == C_{i+1}.IN`.
    ///
    /// The leaf's `[old8 ‖ new8]` door is the REAL rotated roots of the leg the fold mints for that
    /// chain position ([`fixture_rotated_roots`](dregg_multiway_tug::fold::fixture_rotated_roots)),
    /// so the deployed state tooth holds — identical to [`AutomataflMatch::round_leaves`].
    ///
    /// Emitted only at `n = 11` (the sole RoundState-window instantiation); another size is
    /// BLOCKED-not-faked ([`MatchError::NoDescriptor`]).
    pub fn conflict_leaves(&self) -> Result<Vec<LeafBundle>, MatchError> {
        use dregg_automatafl::legc_layout::LegCLayout;
        use dregg_automatafl::legc_witness::{
            RoundStateIn, automatafl_legc_trace, legc_descriptor_ident, legc_round_state_window,
            legc_trace_accepts,
        };
        use dregg_circuit::descriptor_by_name::descriptor_by_name;
        use dregg_circuit::effect_vm::custom_state_binding::{
            BoardWindowBinding, leg_c_roundstate_window_n11,
        };
        use dregg_circuit_prove::joint_turn_aggregation::DescriptorStateLeafSource;
        use dregg_multiway_tug::fold::fixture_rotated_roots;

        if self.conflict_subs.is_empty() {
            return Err(MatchError::Empty);
        }
        let n = self.start.n;
        let cdesc = descriptor_by_name(&legc_descriptor_ident(n))
            .ok_or_else(|| MatchError::NoDescriptor(n, "legc".to_string()))?;

        // The 32-lane RoundState window. `leg_c_roundstate_window_n11` is the pinned n = 11 layout;
        // cross-check it against the descriptor-derived window (fail-closed at any other size).
        let derived: BoardWindowBinding = {
            let (in_slices, out_slices) = legc_round_state_window(n, &cdesc)
                .map_err(|e| MatchError::NoDescriptor(n, format!("legc window: {e}")))?;
            BoardWindowBinding {
                in_slices,
                out_slices,
            }
        };
        let window = leg_c_roundstate_window_n11();
        if window != derived {
            return Err(MatchError::NoDescriptor(
                n,
                "the pinned n=11 RoundState window disagrees with the descriptor's PI layout"
                    .to_string(),
            ));
        }

        let layout = LegCLayout::new(n);
        let rows = 2usize;
        let mut out: Vec<LeafBundle> = Vec::with_capacity(self.conflict_subs.len());
        let mut marks: Vec<dregg_automatafl::reference::Coord> = Vec::new(); // marksIn_0 = ∅

        for (i, subs) in self.conflict_subs.iter().enumerate() {
            let rs = RoundStateIn {
                board: self.start.clone(),
                marks: marks.clone(),
            };
            let mut tr = automatafl_legc_trace(&rs, subs, &cdesc).map_err(|e| {
                MatchError::Lowering(format!("conflict round {i} legc witness-gen: {e}"))
            })?;
            let (old8, new8) = fixture_rotated_roots(out.len() as u64);
            set_state_door(&mut tr.public_inputs, old8, new8);
            // Fail-closed canary: the generated trace must satisfy the Lean Leg C descriptor
            // (the real Ir2Air row-local evaluator) before it is folded.
            if !legc_trace_accepts(&cdesc, &tr) {
                return Err(MatchError::ConflictRefused(i));
            }
            // marksIn for the next round = the marksOut this round produced (ground truth, read off
            // the trace's per-cell marksOut column — never re-derived from a reference oracle).
            marks = decode_marks_out(&tr.row, &layout, n);
            out.push(LeafBundle::descriptor_backed(
                tr.public_inputs.clone(),
                rows,
                DescriptorStateLeafSource {
                    descriptor: cdesc.clone(),
                    base_trace: tr.base_trace(rows),
                    board_window: Some(window.clone()),
                },
            ));
        }
        Ok(out)
    }

    /// **THE ACCUMULATED MARKS** the conflict braid produces — `marksIn` for the terminating clean
    /// round. Fills each conflict round's Leg C trace (gated by the fail-closed
    /// [`legc_trace_accepts`](dregg_automatafl::legc_witness::legc_trace_accepts)) and reads the last
    /// round's `marksOut` off the trace itself (never re-derived from a reference oracle) — the SAME
    /// accumulation [`conflict_leaves`](MultiRoundTurn::conflict_leaves) threads. `∅` when the turn
    /// carries no conflict rounds. No leaf is minted (fill only), so this is fast.
    pub fn accumulated_marks(&self) -> Result<Vec<dregg_automatafl::reference::Coord>, MatchError> {
        use dregg_automatafl::legc_layout::LegCLayout;
        use dregg_automatafl::legc_witness::{
            RoundStateIn, automatafl_legc_trace, legc_descriptor_ident, legc_trace_accepts,
        };
        use dregg_circuit::descriptor_by_name::descriptor_by_name;

        if self.conflict_subs.is_empty() {
            return Ok(Vec::new());
        }
        let n = self.start.n;
        let cdesc = descriptor_by_name(&legc_descriptor_ident(n))
            .ok_or_else(|| MatchError::NoDescriptor(n, "legc".to_string()))?;
        let layout = LegCLayout::new(n);
        let mut marks: Vec<dregg_automatafl::reference::Coord> = Vec::new();
        for (i, subs) in self.conflict_subs.iter().enumerate() {
            let rs = RoundStateIn {
                board: self.start.clone(),
                marks: marks.clone(),
            };
            let tr = automatafl_legc_trace(&rs, subs, &cdesc).map_err(|e| {
                MatchError::Lowering(format!("conflict round {i} legc witness-gen: {e}"))
            })?;
            if !legc_trace_accepts(&cdesc, &tr) {
                return Err(MatchError::ConflictRefused(i));
            }
            marks = decode_marks_out(&tr.row, &layout, n);
        }
        Ok(marks)
    }

    /// **THE TERMINATING CLEAN-ROUND LEAVES.** With prior CONFLICT rounds: the marks-aware **Leg RM**
    /// ([`automatafl_resolve_marks_trace`](dregg_automatafl::resolve_marks_witness::automatafl_resolve_marks_trace),
    /// 20-lane `[board ‖ marks ‖ auto]`) consuming the [`accumulated_marks`](MultiRoundTurn::accumulated_marks),
    /// then the automaton **Leg A** step (11-lane `[board ‖ auto]`). With NO prior conflict: the plain
    /// two-leg round (Leg R resolve + Leg A step), since there are no accumulated marks to consume.
    /// `None` clean submissions ⇒ [`MatchError::Empty`].
    ///
    /// Leg RM re-checks the terminating move against the marks (the M6 legality NOR pin) and exposes
    /// the FULL `board ‖ marks` handoff prefix — the marks half of the `C_last → R` handoff is closed
    /// here (see the type doc for the fold-assembly residuals that remain).
    pub fn clean_leaves(&self) -> Result<Vec<LeafBundle>, MatchError> {
        let subs = self.clean_subs.ok_or(MatchError::Empty)?;
        if self.conflict_subs.is_empty() {
            // No prior conflict ⇒ nothing marked ⇒ the plain two-leg round (marks = ∅).
            return AutomataflMatch::played(self.start.clone(), vec![(subs[0], subs[1])])
                .round_leaves();
        }
        let marks = self.accumulated_marks()?;
        self.resolve_marks_clean_leaves(subs, &marks)
    }

    /// Mint the marks-aware clean round: Leg RM (`old → cMidV4`, consuming `marks`) then Leg A
    /// (`cMidV4 → new`, the automaton). Both carry a state door of the REAL rotated roots the fold
    /// mints for that chain position and are gated by the fail-closed witness-gen canary before
    /// folding — identical discipline to [`AutomataflMatch::round_leaves`]. `marks` is passed
    /// explicitly (rather than always the honest [`accumulated_marks`](MultiRoundTurn::accumulated_marks))
    /// so a canary can hand it a full-braid `marksIn` against a shortened conflict chain and watch the
    /// handoff seam break.
    fn resolve_marks_clean_leaves(
        &self,
        subs: [Move; 2],
        marks: &[dregg_automatafl::reference::Coord],
    ) -> Result<Vec<LeafBundle>, MatchError> {
        use dregg_automatafl::resolve_marks_layout::ResolveMarksLayout;
        use dregg_automatafl::resolve_marks_witness::{
            automatafl_resolve_marks_trace, resolve_marks_board_window,
            resolve_marks_descriptor_ident, resolve_marks_trace_accepts,
        };
        use dregg_automatafl::witness::{
            automatafl_step_trace, step_board_window, step_descriptor_name, step_trace_accepts,
        };
        use dregg_circuit::descriptor_by_name::descriptor_by_name;
        use dregg_circuit_prove::joint_turn_aggregation::DescriptorStateLeafSource;
        use dregg_multiway_tug::fold::fixture_rotated_roots;

        let n = self.start.n;
        let rmdesc = descriptor_by_name(resolve_marks_descriptor_ident(n))
            .ok_or_else(|| MatchError::NoDescriptor(n, "resolve-marks".to_string()))?;
        let sdesc = descriptor_by_name(&step_descriptor_name(n))
            .ok_or_else(|| MatchError::NoDescriptor(n, "step".to_string()))?;
        let rmwin = resolve_marks_board_window(n, &rmdesc)
            .map_err(|e| MatchError::NoDescriptor(n, format!("resolve-marks window: {e}")))?;
        let awin = step_board_window(n, &sdesc)
            .map_err(|e| MatchError::NoDescriptor(n, format!("step window: {e}")))?;
        let layout = ResolveMarksLayout::new(n);
        let rows = 2usize;
        let mut out: Vec<LeafBundle> = Vec::with_capacity(2);

        // ---- Leg RM: marks-aware resolve, old -> cMidV4, consuming the accumulated marks. ----
        let mut rt = automatafl_resolve_marks_trace(&self.start, &subs, marks, &rmdesc)
            .map_err(|e| MatchError::Lowering(format!("clean resolve-marks witness-gen: {e}")))?;
        let (r_old8, r_new8) = fixture_rotated_roots(out.len() as u64);
        set_state_door(&mut rt.public_inputs, r_old8, r_new8);
        // Fail-closed: a marks-illegal terminating move (a move onto/out of an accumulated mark)
        // fills but is REJECTED by the M6 legality NOR pin here, before any proving.
        if !resolve_marks_trace_accepts(&rmdesc, &rt) {
            return Err(MatchError::ResolveRefused(0));
        }
        let mid = rt.mid_board(&layout);
        out.push(LeafBundle::descriptor_backed(
            rt.public_inputs.clone(),
            rows,
            DescriptorStateLeafSource {
                descriptor: rmdesc.clone(),
                base_trace: rt.base_trace(rows),
                board_window: Some(rmwin.clone()),
            },
        ));

        // ---- Leg A: step the automaton, cMidV4 -> new (11-lane pack||auto window). ----
        let mut st = automatafl_step_trace(&mid, &sdesc)
            .map_err(|e| MatchError::Lowering(format!("clean step witness-gen: {e}")))?;
        let (a_old8, a_new8) = fixture_rotated_roots(out.len() as u64);
        set_state_door(&mut st.public_inputs, a_old8, a_new8);
        if !step_trace_accepts(&sdesc, &st) {
            return Err(MatchError::D1Refused(0));
        }
        out.push(LeafBundle::descriptor_backed(
            st.public_inputs.clone(),
            rows,
            DescriptorStateLeafSource {
                descriptor: sdesc.clone(),
                base_trace: st.base_trace(rows),
                board_window: Some(awin.clone()),
            },
        ));

        Ok(out)
    }
}

/// Decode a Leg C trace's per-cell `marksOut` overlay into a coordinate list (the next round's
/// `marksIn`). A cell is marked iff its `c_marks_out_cell` column is `1`.
fn decode_marks_out(
    row: &[BabyBear],
    layout: &dregg_automatafl::legc_layout::LegCLayout,
    n: usize,
) -> Vec<dregg_automatafl::reference::Coord> {
    (0..n * n)
        .filter(|&c| row[layout.c_marks_out_cell(c)] == BabyBear::ONE)
        .map(|c| ((c % n) as i32, (c / n) as i32))
        .collect()
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

    /// **Pin a game's board anchor ONCE — idempotent and IMMUTABLE.** The first call opens the
    /// board against `anchor` (via [`GameBoard::open`]); every later call returns the
    /// already-open universe and IGNORES the passed `anchor`. The trust anchor is board CONFIG
    /// (a committed canonical reference, distributed like a SNARK VK) — a submitted proof, or
    /// any later caller, can NEVER define or replace the genesis / WIN roots a submission is
    /// verified against.
    ///
    /// This is the anti-capture seam for the submission path: a caller that opened the board
    /// per submission with `open(game, match_anchor(&submitted_proof))` let the FIRST proof mint
    /// the board's trust anchor (self-comparing the genesis / win checks) and — because the
    /// content [`UniverseId`] is a per-game constant and `Registry::publish` is `or_insert` —
    /// froze that first anchor forever, refusing every later distinct submission. Pinning the
    /// anchor ONCE from a submission-independent source through this method removes both.
    pub fn ensure_open(&mut self, game: Game, anchor: ProofAnchor) -> UniverseId {
        if let Some(&id) = self.universes.get(&game) {
            return id;
        }
        self.open(game, anchor)
    }

    /// Whether a game's proof-carrying board is already open (its [`ProofAnchor`] pinned).
    pub fn is_open(&self, game: Game) -> bool {
        self.universes.contains_key(&game)
    }

    /// The [`ProofAnchor`] a game's board is pinned to, if open — the immutable VK + genesis +
    /// WIN roots every submission for this game is verified against. Read it back to confirm the
    /// anchor is the committed canonical one, NOT one captured from a submitted proof.
    pub fn anchor(&self, game: Game) -> Option<&ProofAnchor> {
        let id = self.universes.get(&game)?;
        self.registry.universe(*id)?.proof_anchor()
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
