//! # The automatafl match DEPLOYED on the real executor.
//!
//! The proven Lean descriptors (Leg R + Leg A, see the crate docs) prove `new == apply_turn(old,
//! moves)` in-circuit via [`crate::witness`] / [`crate::resolve_witness`]. This module is the
//! other half of the same game: the n=2 match hosted on a real [`spween_dregg::WorldCell`] (the
//! deployed `EmbeddedExecutor` + ledger), so a PLAY is one cap-bounded verified turn with a real
//! [`dregg_app_framework::TurnReceipt`] — the substrate the [`crate::surface::AutomataflOffering`]
//! drives (every move is a receipt).
//!
//! The STATE is declared as a [`dregg_schema::Schema`] and lowered by the CONSUMED allocator
//! ([`allocate_checked`]) to a Legal slot/heap layout: 15 scalar registers (the turn counter, the
//! phase, the two sealed commitments, the two selections, the two revealed moves, the automaton
//! coordinates, the winner) and the 121 board squares on heap keys `16..137`.
//!
//! **THE BOARD IS THE STOCK 11×11 TWO-PLAYER GAME** ([`crate::reference::stock_two_player`], the
//! byte-for-byte transcription of the automatafl reference opening) with the real four-corner goal
//! set ([`crate::reference::GOAL_CORNERS_2P`]). That is the size the Lean descriptors are EMITTED
//! at (`dregg-automatafl-{step,resolve}-d1-n11`), so a played match LOWERS: the former 5×5
//! mini-variant had no emitted descriptor at all, so every fold of a played match was
//! `MatchError::NoDescriptor`-blocked (blocked-not-faked) and no automatafl match could rank.
//!
//! The PLAY TEETH are a hand-rolled [`CellProgram::Cases`] over those allocator-resolved slots —
//! the SIMULTANEOUS-move (commit → reveal → resolve) discipline, enforced by the executor:
//!
//! * **`select`** — pick your source square. The board is [`StateConstraint::Immutable`] and so is
//!   `turn_no`: a "selection" that also moves a piece, or advances the turn, is REFUSED.
//! * **`commit`** — seal your move (the executor stores only the COMMITMENT). Board + `turn_no`
//!   immutable; `commits` [`StateConstraint::StrictMonotonic`] (a replayed commit cannot land).
//! * **`reveal`** — open your sealed move. Board + `turn_no` + BOTH commitments immutable (a
//!   reveal that rewrites the seal it is opening is REFUSED); `reveals` strictly monotone.
//! * **`resolve`** — the resolution: `turn_no` strictly monotone, every board square pinned to a
//!   real particle code by [`HeapAtom::MemberOf`] `{0,1,2,3}` (a conjured particle is REFUSED), the
//!   automaton coordinates range-pinned to the board, and `winner` [`StateConstraint::WriteOnce`]
//!   (a claimed win cannot be overwritten).
//!
//! `genesis` is the one permissive case (it seeds the opening board + the registers the relational
//! teeth read as an `old` value). The BOARD TRANSITION itself (`new == apply_turn(old, moves)`) is
//! re-checked off-circuit by [`crate::reference::apply_turn`] (the witness oracle the AIR pins) —
//! the executor teeth are the state discipline, the AIR is the transition proof.

use std::collections::BTreeMap;
use std::sync::Arc;

use dregg_app_framework::{
    CellId, CellProgram, Effect, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    field_from_u64, symbol,
};
use dregg_cell::program::HeapAtom;
use dregg_schema::layout::{CheckedLayout, Slot, allocate_checked};
use dregg_schema::schema::Schema;
use dregg_schema::{genesis_oneshot_teeth, genesis_sentinel_freeze};
use spween_dregg::{CompiledStory, WorldCell, WorldError};

use crate::reference::{Board, Coord, GOAL_CORNERS_2P, N11, stock_two_player};

/// The scene id that fixes the deterministic world-cell identity.
pub const SCENE_ID: &str = "dregg-automatafl/n2";
/// The permissive seeding method.
pub const GENESIS: &str = "genesis";
/// Pick your source square (no board change).
pub const SELECT: &str = "select";
/// Seal your move (the executor stores the commitment only).
pub const COMMIT: &str = "commit";
/// Open your sealed move.
pub const REVEAL: &str = "reveal";
/// Resolve the simultaneous turn (conflicts dropped, moves applied, the automaton steps).
pub const RESOLVE: &str = "resolve";

/// The board edge — the REAL stock two-player game, 11×11, and the size the Lean descriptors are
/// emitted at. The played surface and the proven descriptors are the SAME `n`: this is what makes
/// a played match foldable at all.
pub const N: usize = N11;
/// The number of board squares (one heap key each).
pub const CELLS: usize = N * N;

/// The 15 register components, in allocation order (slots `0..15`).
const REGISTERS: [&str; 15] = [
    "turn_no",  // the resolved-turn counter (strictly monotone on `resolve`)
    "phase",    // 0 = commit, 1 = reveal, 2 = over
    "winner",   // 0 = none, 1 = seat A, 2 = seat B (write-once)
    "commits",  // total sealed commitments (strictly monotone on `commit`)
    "reveals",  // total opened commitments (strictly monotone on `reveal`)
    "a_commit", // seat A's sealed move commitment (immutable under `reveal`)
    "b_commit", // seat B's sealed move commitment
    "a_sel",    // seat A's selected source, `index + 1` (0 = none)
    "b_sel",    // seat B's selected source
    "a_frm",    // seat A's REVEALED source, `index + 1` (0 = unrevealed)
    "a_to",     // seat A's REVEALED destination, `index + 1`
    "b_frm",    // seat B's revealed source
    "b_to",     // seat B's revealed destination
    "auto_x",   // the automaton's x (range-pinned on `resolve`)
    "auto_y",   // the automaton's y
];

/// The heap component name of board square `idx` (`idx = y*N + x`).
pub fn cell_name(idx: usize) -> String {
    format!("cell_{idx}")
}

/// The declared schema: 15 register components + the [`CELLS`] board squares as heap collections.
pub fn schema() -> Schema {
    let mut s = Schema::new(SCENE_ID)
        .stat("turn_no", 0, 1024)
        .stat("phase", 0, 2)
        .identity("winner")
        .stat("commits", 0, 4096)
        .stat("reveals", 0, 4096)
        .identity("a_commit")
        .identity("b_commit")
        .stat("a_sel", 0, CELLS as u64)
        .stat("b_sel", 0, CELLS as u64)
        .stat("a_frm", 0, CELLS as u64)
        .stat("a_to", 0, CELLS as u64)
        .stat("b_frm", 0, CELLS as u64)
        .stat("b_to", 0, CELLS as u64)
        .stat("auto_x", 0, (N - 1) as u64)
        .stat("auto_y", 0, (N - 1) as u64);
    for idx in 0..CELLS {
        s = s.collection(cell_name(idx));
    }
    s
}

/// The consumed, Legal-checked layout + the hand-rolled play teeth.
pub struct Deployment {
    /// The allocator's Legal-checked slot/heap layout.
    pub layout: CheckedLayout,
}

impl Deployment {
    /// Allocate + Legal-check the schema (the translation-validation allocator).
    pub fn new() -> Self {
        let layout = allocate_checked(&schema()).expect("automatafl layout is Legal");
        Deployment { layout }
    }

    /// Resolve a register component to its slot index.
    pub fn reg(&self, name: &str) -> u8 {
        match self.layout.resolve(name) {
            Some(Slot::Register(r)) => r,
            other => panic!("`{name}` is not a register: {other:?}"),
        }
    }

    /// Resolve a heap component to its key.
    pub fn key(&self, name: &str) -> u64 {
        match self.layout.resolve(name) {
            Some(Slot::Heap(k)) => k,
            other => panic!("`{name}` is not a heap key: {other:?}"),
        }
    }

    /// The heap key of board square `idx`.
    pub fn cell_key(&self, idx: usize) -> u64 {
        self.key(&cell_name(idx))
    }

    /// Every board square is IMMUTABLE under this method (the commit-phase discipline: a
    /// selection / a seal / a reveal cannot move a piece).
    fn board_immutable(&self) -> Vec<StateConstraint> {
        (0..CELLS)
            .map(|idx| StateConstraint::HeapField {
                key: self.cell_key(idx),
                atom: HeapAtom::Immutable,
            })
            .collect()
    }

    /// Every board square holds a REAL particle code (`0 = vacuum, 1 = repulsor, 2 = attractor,
    /// 3 = automaton`) — the resolution tooth: a conjured particle is refused.
    fn board_particles(&self) -> Vec<StateConstraint> {
        (0..CELLS)
            .map(|idx| StateConstraint::HeapField {
                key: self.cell_key(idx),
                atom: HeapAtom::MemberOf {
                    set: vec![0, 1, 2, 3],
                },
            })
            .collect()
    }

    /// The hand-rolled play-teeth program (the commit → reveal → resolve discipline),
    /// with the ONE-SHOT genesis guard installed (the deployed program).
    pub fn program(&self) -> CellProgram {
        self.build_program(true)
    }

    /// **CANARY ONLY — the historical write-hatch, deliberately reopened.** The program
    /// with the genesis guard REMOVED: genesis carries EMPTY teeth and the play cases do
    /// NOT freeze the sentinel — the byte-identical pre-fix program. A post-deploy
    /// `apply_raw(GENESIS, [SetField(slot, V)])` this build ADMITS the real
    /// [`Self::program`] REFUSES, which proves the one-shot guard is load-bearing.
    #[doc(hidden)]
    pub fn program_hatch_reopened(&self) -> CellProgram {
        self.build_program(false)
    }

    /// Build the play teeth. When `oneshot` (the deployed program), the genesis case is
    /// the `0 → 1` one-shot on [`spween_dregg::GENESIS_DONE_EXT_KEY`]
    /// ([`genesis_oneshot_teeth`]: `Equals{1} ∧ DeltaEquals{1}`, admissible exactly once
    /// at deploy/seed, jointly unsatisfiable for every later genesis turn) and every
    /// non-genesis case FREEZES that sentinel ([`genesis_sentinel_freeze`]), so a
    /// post-deploy genesis staple is refused regardless of which slot it targets — with
    /// no per-slot dependence — and no move can reset the sentinel to re-open genesis.
    /// `WorldCell` births the sentinel at deploy and injects the `0 → 1` write on the
    /// `genesis` method automatically (it keys off this genesis-case `HeapField`). When
    /// `false`, the historical permissive genesis (the universal write-hatch) — canary
    /// only.
    fn build_program(&self, oneshot: bool) -> CellProgram {
        let case = |name: &str, constraints: Vec<StateConstraint>| TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol(name),
            },
            constraints,
        };

        let turn_no = self.reg("turn_no");
        let winner = self.reg("winner");

        // `select`: the board and the turn cannot move.
        let mut select = self.board_immutable();
        select.push(StateConstraint::Immutable { index: turn_no });
        select.push(StateConstraint::Immutable { index: winner });

        // `commit`: the board and the turn cannot move; a commitment is a strictly-new seal.
        let mut commit = self.board_immutable();
        commit.push(StateConstraint::Immutable { index: turn_no });
        commit.push(StateConstraint::Immutable { index: winner });
        commit.push(StateConstraint::StrictMonotonic {
            index: self.reg("commits"),
        });

        // `reveal`: the board, the turn and BOTH seals are frozen — a reveal opens a seal, it
        // never rewrites it.
        let mut reveal = self.board_immutable();
        reveal.push(StateConstraint::Immutable { index: turn_no });
        reveal.push(StateConstraint::Immutable { index: winner });
        reveal.push(StateConstraint::Immutable {
            index: self.reg("a_commit"),
        });
        reveal.push(StateConstraint::Immutable {
            index: self.reg("b_commit"),
        });
        reveal.push(StateConstraint::StrictMonotonic {
            index: self.reg("reveals"),
        });

        // `resolve`: the turn advances, every square holds a real particle, the automaton stays on
        // the board, and a declared winner is write-once.
        let mut resolve = self.board_particles();
        resolve.push(StateConstraint::StrictMonotonic { index: turn_no });
        resolve.push(StateConstraint::WriteOnce { index: winner });
        resolve.push(StateConstraint::FieldLte {
            index: self.reg("auto_x"),
            value: field_from_u64((N - 1) as u64),
        });
        resolve.push(StateConstraint::FieldLte {
            index: self.reg("auto_y"),
            value: field_from_u64((N - 1) as u64),
        });
        resolve.push(StateConstraint::FieldLte {
            index: self.reg("phase"),
            value: field_from_u64(2),
        });

        // The genesis case: the one permissive seeding method (it seeds the opening board
        // + the registers the relational teeth read as an `old` value). It cannot carry
        // per-slot teeth without refusing a legit blank-baseline seed — so an EMPTY
        // genesis case is a UNIVERSAL post-deploy write-hatch: `apply_raw(GENESIS,
        // [SetField(any_slot, V)])` re-dispatches the permissive case and commits an
        // arbitrary write to any slot, routing around every play tooth (the stapleable-slot
        // hole class). The one-shot guard closes it at the ROOT for every slot at once:
        // genesis becomes the `0 → 1` sentinel transition, and each play case freezes the
        // sentinel so no move can reset it.
        let genesis = if oneshot {
            for teeth in [&mut select, &mut commit, &mut reveal, &mut resolve] {
                teeth.push(genesis_sentinel_freeze());
            }
            genesis_oneshot_teeth()
        } else {
            Vec::new()
        };

        CellProgram::Cases(vec![
            case(GENESIS, genesis),
            case(SELECT, select),
            case(COMMIT, commit),
            case(REVEAL, reveal),
            case(RESOLVE, resolve),
        ])
    }

    /// The compiled story to install on the world-cell (the deployed one-shot program).
    pub fn story(&self) -> CompiledStory {
        self.story_with(self.program())
    }

    /// The compiled story carrying a chosen `program` — the real [`Self::story`] uses the
    /// one-shot [`Self::program`]; the write-hatch canary uses
    /// [`Self::program_hatch_reopened`].
    #[doc(hidden)]
    pub fn story_with(&self, program: CellProgram) -> CompiledStory {
        let mut var_slots = BTreeMap::new();
        for name in REGISTERS {
            var_slots.insert(name.to_string(), self.reg(name) as u64);
        }
        CompiledStory {
            scene_id: SCENE_ID.to_string(),
            var_slots,
            has_slots: BTreeMap::new(),
            passage_index: BTreeMap::new(),
            program,
            fully_gated: BTreeMap::new(),
        }
    }
}

impl Default for Deployment {
    fn default() -> Self {
        Self::new()
    }
}

/// The full committed match state — the 15 registers + the [`CELLS`] board squares. Every turn writes it
/// in full (the witnessed post-state the teeth re-check).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchState {
    /// The resolved-turn counter.
    pub turn_no: u64,
    /// `0 = commit, 1 = reveal, 2 = over`.
    pub phase: u64,
    /// `0 = none, 1 = seat A, 2 = seat B`.
    pub winner: u64,
    /// Total sealed commitments across the match.
    pub commits: u64,
    /// Total opened commitments across the match.
    pub reveals: u64,
    /// Each seat's sealed move commitment (`0` = unsealed).
    pub commit: [u64; 2],
    /// Each seat's selected source, `index + 1` (`0` = none).
    pub sel: [u64; 2],
    /// Each seat's REVEALED source, `index + 1` (`0` = unrevealed).
    pub frm: [u64; 2],
    /// Each seat's REVEALED destination, `index + 1` (`0` = unrevealed).
    pub to: [u64; 2],
    /// The automaton's coordinates.
    pub auto: Coord,
    /// The [`CELLS`] board squares (`cells[y*N + x]` ∈ `{0,1,2,3}`).
    pub cells: Vec<u8>,
}

impl MatchState {
    /// The reference [`Board`] this committed state denotes (the oracle the AIR pins).
    pub fn board(&self) -> Board {
        Board {
            n: N,
            cells: self.cells.clone(),
            auto: self.auto,
            col_rule: true,
        }
    }
}

/// The automatafl match, deployed and DRIVEN on a real world-cell.
pub struct AutomataflGame {
    dep: Deployment,
    world: WorldCell,
}

impl AutomataflGame {
    /// Deploy the story on a real world-cell (deterministic in `SCENE_ID` + `seed`).
    pub fn deploy(seed: u8) -> Result<Self, WorldError> {
        let dep = Deployment::new();
        let story = dep.story();
        let world = WorldCell::deploy_compiled(Arc::new(story), seed)?;
        Ok(AutomataflGame { dep, world })
    }

    /// **CANARY ONLY.** Deploy with the genesis guard REMOVED (the historical write-hatch,
    /// [`Deployment::program_hatch_reopened`]). Used to prove the one-shot guard is
    /// load-bearing: a post-deploy genesis staple this build ADMITS the real
    /// [`Self::deploy`] REFUSES.
    #[doc(hidden)]
    pub fn deploy_hatch_reopened(seed: u8) -> Result<Self, WorldError> {
        let dep = Deployment::new();
        let story = dep.story_with(dep.program_hatch_reopened());
        let world = WorldCell::deploy_compiled(Arc::new(story), seed)?;
        Ok(AutomataflGame { dep, world })
    }

    /// The Legal-checked deployment (slot/heap resolution).
    pub fn dep(&self) -> &Deployment {
        &self.dep
    }

    /// The deployed world-cell.
    pub fn world(&self) -> &WorldCell {
        &self.world
    }

    /// The deployed cell id.
    pub fn cell(&self) -> CellId {
        self.world.cell_id()
    }

    /// Every `SetField` effect writing `st` in full (15 registers + [`CELLS`] board keys).
    fn effects_for(&self, st: &MatchState) -> Vec<Effect> {
        let cell = self.cell();
        let mut effects = Vec::with_capacity(REGISTERS.len() + CELLS);
        let mut set = |name: &str, v: u64| {
            effects.push(Effect::SetField {
                cell,
                index: self.dep.reg(name) as u64,
                value: field_from_u64(v),
            });
        };
        set("turn_no", st.turn_no);
        set("phase", st.phase);
        set("winner", st.winner);
        set("commits", st.commits);
        set("reveals", st.reveals);
        set("a_commit", st.commit[0]);
        set("b_commit", st.commit[1]);
        set("a_sel", st.sel[0]);
        set("b_sel", st.sel[1]);
        set("a_frm", st.frm[0]);
        set("a_to", st.to[0]);
        set("b_frm", st.frm[1]);
        set("b_to", st.to[1]);
        set("auto_x", st.auto.0.max(0) as u64);
        set("auto_y", st.auto.1.max(0) as u64);
        drop(set);
        for idx in 0..CELLS {
            effects.push(Effect::SetField {
                cell,
                index: self.dep.cell_key(idx) as u64,
                value: field_from_u64(st.cells[idx] as u64),
            });
        }
        effects
    }

    /// Seed the opening match state under the permissive genesis method.
    pub fn seed(&self, st: &MatchState) -> Result<TurnReceipt, WorldError> {
        self.world.apply_raw(GENESIS, self.effects_for(st))
    }

    /// Commit a full match state under `method` — the primitive every play uses. The executor's
    /// teeth re-check the witnessed post-state; an illegal one is a real [`WorldError::Refused`].
    pub fn commit_state(&self, method: &str, st: &MatchState) -> Result<TurnReceipt, WorldError> {
        self.world.apply_raw(method, self.effects_for(st))
    }

    /// Drive a RAW turn (the forgery tests): whatever `effects`, under `method`.
    pub fn commit_raw(
        &self,
        method: &str,
        effects: Vec<Effect>,
    ) -> Result<TurnReceipt, WorldError> {
        self.world.apply_raw(method, effects)
    }

    /// A `SetField` on a named register (a forgery-test builder).
    pub fn reg_effect(&self, name: &str, v: u64) -> Effect {
        Effect::SetField {
            cell: self.cell(),
            index: self.dep.reg(name) as u64,
            value: field_from_u64(v),
        }
    }

    /// A `SetField` on a board square (a forgery-test builder).
    pub fn cell_effect(&self, idx: usize, v: u64) -> Effect {
        Effect::SetField {
            cell: self.cell(),
            index: self.dep.cell_key(idx) as u64,
            value: field_from_u64(v),
        }
    }

    /// Read a register off the committed cell state.
    pub fn read_reg(&self, name: &str) -> u64 {
        self.world.snapshot()[self.dep.reg(name) as usize]
    }

    /// Read a board square off the committed cell state.
    pub fn read_cell(&self, idx: usize) -> u8 {
        self.world.read_heap(self.dep.cell_key(idx)).unwrap_or(0) as u8
    }

    /// Reconstruct the COMMITTED match state off the cell — compared against the reference to
    /// prove the executor reproduces the game exactly (the translation-validation shape).
    pub fn read_state(&self) -> MatchState {
        MatchState {
            turn_no: self.read_reg("turn_no"),
            phase: self.read_reg("phase"),
            winner: self.read_reg("winner"),
            commits: self.read_reg("commits"),
            reveals: self.read_reg("reveals"),
            commit: [self.read_reg("a_commit"), self.read_reg("b_commit")],
            sel: [self.read_reg("a_sel"), self.read_reg("b_sel")],
            frm: [self.read_reg("a_frm"), self.read_reg("b_frm")],
            to: [self.read_reg("a_to"), self.read_reg("b_to")],
            auto: (
                self.read_reg("auto_x") as i32,
                self.read_reg("auto_y") as i32,
            ),
            cells: (0..CELLS).map(|i| self.read_cell(i)).collect(),
        }
    }
}

/// The coordinate of board index `idx` (`idx = y*N + x`).
pub fn coord_of(idx: usize) -> Coord {
    ((idx % N) as i32, (idx / N) as i32)
}

/// The board index of coordinate `c` (in-bounds only).
pub fn index_of(c: Coord) -> Option<usize> {
    if c.0 >= 0 && (c.0 as usize) < N && c.1 >= 0 && (c.1 as usize) < N {
        Some((c.1 as usize) * N + (c.0 as usize))
    } else {
        None
    }
}

/// **The opening board — the STOCK two-player position** ([`stock_two_player`]): the automaton
/// dead centre at `(5,5)`, the repulsor/attractor ring around the flanks, the four attractor pairs
/// on the `y ∈ {4,6}` files. This is the reference game's own opening, not an invented mini-board,
/// and it is the position the emitted `n=11` Lean descriptors adjudicate.
pub fn opening_board() -> Board {
    let b = stock_two_player();
    debug_assert_eq!(b.n, N, "the played opening is the emitted-descriptor size");
    b
}

/// **The four goal corners of the stock two-player game**, each tagged with its owning seat
/// (`0` = seat A, `1` = seat B) — [`crate::reference::GOAL_CORNERS_2P`]. Per the two-player rule
/// each player owns the two corners in one row: seat A the `y = 0` pair, seat B the `y = 10` pair.
/// The automaton stepping onto a corner wins for that corner's owner.
pub const GOALS: [(Coord, u32); 4] = GOAL_CORNERS_2P;

/// The two goal corners seat `who` (`0`/`1`) owns.
pub fn goals_of(who: u32) -> Vec<Coord> {
    GOALS
        .iter()
        .filter(|(_, w)| *w == who)
        .map(|(c, _)| *c)
        .collect()
}

/// The seat whose goal corner the automaton currently occupies, or `None` — the deployed win check
/// ([`crate::reference::win_owner`] over [`GOALS`], the reference `try_complete_round` goal scan).
pub fn winner_of(b: &Board) -> Option<u32> {
    crate::reference::win_owner(b, &GOALS)
}

#[cfg(test)]
mod played_size_is_the_proven_size {
    use super::*;

    /// **THE STANDING GATE.** The board the surface PLAYS must be the board the Lean descriptors
    /// are EMITTED at. When they diverged (the surface on an invented 5×5, every descriptor at
    /// n=11) `descriptor_by_name` returned `None` for the played size, so every fold of a played
    /// match was `NoDescriptor`-blocked and no automatafl match could ever rank — a failure that
    /// was invisible from inside the surface, because the surface itself was perfectly green.
    /// This test fails the moment that divergence reappears.
    #[test]
    fn the_played_board_size_has_both_emitted_lean_descriptors() {
        use crate::resolve_witness::resolve_descriptor_ident;
        use crate::witness::step_descriptor_name;
        use dregg_circuit::descriptor_by_name::descriptor_by_name;

        let b = opening_board();
        assert_eq!(b.n, N, "the opening board IS the declared board size");
        assert_eq!(b.cells.len(), CELLS);
        assert!(
            descriptor_by_name(&step_descriptor_name(N)).is_some(),
            "the played size {N} has NO emitted Lean STEP descriptor — every fold of a played \
             match would be NoDescriptor-blocked"
        );
        assert!(
            descriptor_by_name(resolve_descriptor_ident(N)).is_some(),
            "the played size {N} has NO emitted Lean RESOLVE descriptor — the two-leg fold that \
             attests the players' MOVES cannot be minted"
        );
    }

    /// Every goal corner is on the board, and the two seats own two corners each.
    #[test]
    fn the_goal_corners_are_the_stock_four() {
        assert_eq!(goals_of(0).len(), 2, "seat A owns two corners");
        assert_eq!(goals_of(1).len(), 2, "seat B owns two corners");
        for (c, _) in GOALS {
            assert!(index_of(c).is_some(), "goal {c:?} is on the played board");
        }
        // The opening is not already won.
        assert_eq!(winner_of(&opening_board()), None);
    }
}
