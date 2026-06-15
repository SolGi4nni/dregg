//! # TUSSLE — a Toribash-style verified joint-combat match (Starbridge usecase app)
//!
//! Two **figures** fight by posing their **joints**. The delicious architecture pun: a figure's
//! joints are set in a **2-party joint turn**. TUSSLE is the forcing-function demo of deos's
//! hyperadvanced features — it COMPOSES the real primitives (the sealed commit, the typed `sym`
//! enum atoms, dregg cells, the verified per-asset executor) into a small, deterministic, verifiable
//! fighting game. There is NO toy combat engine: every guarantee is a real one the substrate
//! already enforces.
//!
//! ## The mapping (Toribash → deos)
//!
//! | Toribash                          | deos / dregg                                              |
//! |-----------------------------------|-----------------------------------------------------------|
//! | a fighter                         | a **figure** = a dregg **cell** ([`dregg_cell::CellState`])|
//! | a joint (knee, elbol, …)          | a **`sym` slot** of the figure cell                       |
//! | a joint state (Relax/Contract/…)  | a [`JointState`] enum case (a `Value.sym` identity)       |
//! | "you can't see my move yet"       | a **sealed commitment** ([`MoveCommit::seal`], fog-of-war)|
//! | both players lock in, then it runs| **commit → reveal → resolve** ([`Frame`])                 |
//! | the frame steps the physics       | a **deterministic resolution** = a cell-program           |
//! | the engine moves bodies + scores  | a **2-party joint turn**: score deltas folded through the |
//! |                                   | **verified executor** ([`dregg_intent::verified_settle`]) |
//!
//! ## What makes it verifiable (the three real primitives composed)
//!
//! 1. **The sealed commit (fog-of-war).** A move is a joint-state vector. Before the reveal, a
//!    player publishes only `seal(figure, joints, nonce) = BLAKE3(…)` — the SAME commit-reveal
//!    construction the sealed-auction app uses. The commitment HIDES the joints (the nonce blinds
//!    even the small joint-vector space) and BINDS the player to exactly one move: a peeker who
//!    changes their joints after seeing the opponent reveal hashes to a different seal that is not
//!    among the commitments, so the reveal is refused. The fog-of-war tooth
//!    ([`Frame::opponent_move_is_sealed`]) witnesses that the opponent's joints are unreadable from
//!    the sealed commitment alone.
//!
//! 2. **The joint-state-is-an-enum gate (the typed `sym` atom).** A joint slot's value must be one
//!    of the [`JointState`] enum cases — never an arbitrary scalar. That tooth is the freshly-landed
//!    typed atom [`dregg_cell::StateConstraint::SymMemberOf`] (the Rust image of the Lean
//!    `Pred.symMemberOf`, `metatheory/Dregg2/Exec/PredAlgebra.lean`), evaluated by the REAL
//!    [`dregg_cell::CellProgram::evaluate`] — the exact gate the executor runs every turn. A figure
//!    that tries to drive a joint to an out-of-enum value is REFUSED in-band ([`Figure::pose`]).
//!
//! 3. **The 2-party joint turn (the verified executor).** The deterministic resolution emits the
//!    contact **score deltas** as a balanced **ring of legs**, and folds them through the verified
//!    per-asset executor ([`dregg_intent::verified_settle::settle_ring_verified`], the Rust mirror
//!    of the Lean `Ring.settleRing`). The figures' score cells are the ledger accounts; the contact
//!    resolution is a deterministic function over the two revealed joint vectors, emitted as ring
//!    legs. On every native build (Lean unconditional) each leg is ALSO cross-checked against the
//!    REAL Lean executor export, leg by leg — so an advanced frame's score move IS a verified,
//!    conserving executor turn, not a Rust-only shadow.
//!
//! ## Cap ∧ state gating
//!
//! A player may set joints only on THEIR figure (the cap tooth) during THEIR commit phase (the
//! state tooth). The cap tooth is enforced by binding every [`MoveCommit`] to a `figure` cell id
//! and refusing a reveal whose commit was authored against the wrong figure
//! ([`Frame::reveal`] → [`TussleError::WrongFigure`]); the state tooth is the `Commit → Reveal →
//! Resolved` phase gate (a reveal before the commit phase closes is refused). This is the same
//! cap∧state conjunction the deos `GatedAffordance` (`app-framework`) models; here both teeth are
//! load-bearing and tested (`src/tests.rs`).

#![forbid(unsafe_code)]

use std::collections::BTreeMap;

use dregg_cell::{CellProgram, CellState, FieldElement, StateConstraint, field_from_u64};
use dregg_intent::verified_settle::{
    VerifiedLedger, VerifiedLeg, VerifiedSettleError, settle_ring_verified,
};

pub mod resolution;

pub use resolution::{Contact, FrameResolution, resolve_contact};

/// A cell id, restricted to the low byte the verified per-asset ledger indexes by (the Rust view of
/// the Lean `CellId`). Each figure is a cell, identified by this id.
pub type FigureId = u8;

/// A 32-byte score asset — the column the verified executor moves when a figure scores. The two
/// figures' score cells hold balances in this asset; a contact transfers `points` of it.
pub type ScoreAsset = [u8; 32];

/// A 32-byte sealed move commitment.
pub type MoveSeal = [u8; 32];

/// The score asset all matches are denominated in (a fixed well-known column).
pub const SCORE_ASSET: ScoreAsset = {
    let mut a = [0u8; 32];
    a[0] = 0x70; // 'p' for "points"
    a
};

/// The number of joints a figure has. A small fixed roster keeps the resolution deterministic and
/// the cell's slot use within the 16 user slots. Each joint is one `sym` slot of the figure cell.
pub const N_JOINTS: usize = 4;

// ---------------------------------------------------------------------------
// JointState — the `sym` enum (a joint slot's value is one of these cases)
// ---------------------------------------------------------------------------

/// The state of a single joint — the `Value.sym` enum at the heart of the game. Each case is an
/// interned identity (NOT an orderable scalar): the typed-`sym` atom [`StateConstraint::SymMemberOf`]
/// pins a joint slot to exactly this set, mirroring the Lean `Pred.symMemberOf`
/// (`metatheory/Dregg2/Exec/PredAlgebra.lean`).
///
/// The four states give a joint a directional influence on the figure's motion when the frame
/// resolves (see [`JointState::drive`]): `Contract` pulls the figure forward, `Extend` pushes it
/// back, `Hold` braces (resists being moved), `Relax` is limp (no influence, easy to knock).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u64)]
pub enum JointState {
    /// Limp — no drive, offers no brace (the figure can be pushed freely here).
    Relax = 0,
    /// Pull — drives the figure toward the opponent (forward influence).
    Contract = 1,
    /// Brace — resists being moved (a defensive lock; cancels an opposing push).
    Hold = 2,
    /// Push — drives the figure away from the opponent (backward influence).
    Extend = 3,
}

impl JointState {
    /// The set of all joint-state cases, as the `sym` enum the typed atom pins a slot to. This is
    /// the `set` of [`StateConstraint::SymMemberOf`] — "this slot is one of the JointState cases".
    pub const ALL: [JointState; 4] = [
        JointState::Relax,
        JointState::Contract,
        JointState::Hold,
        JointState::Extend,
    ];

    /// This joint state's interned `sym` value (its enum case as the `u64` identity lane). The
    /// figure cell stores `field_from_u64(self.sym())` in the joint's slot; the executor's
    /// `SymMemberOf` reads it back via `field_to_u64`.
    pub fn sym(self) -> u64 {
        self as u64
    }

    /// Reconstruct a joint state from its interned `sym` value (the inverse of [`JointState::sym`]).
    /// `None` for a value outside the enum — exactly the case [`StateConstraint::SymMemberOf`]
    /// refuses (an out-of-enum joint slot).
    pub fn from_sym(sym: u64) -> Option<JointState> {
        match sym {
            0 => Some(JointState::Relax),
            1 => Some(JointState::Contract),
            2 => Some(JointState::Hold),
            3 => Some(JointState::Extend),
            _ => None,
        }
    }

    /// The set of legal `sym` values — the enum membership set the typed atom pins each joint slot
    /// to. This is what [`Figure::joint_program`] feeds [`StateConstraint::SymMemberOf`].
    pub fn enum_set() -> Vec<u64> {
        JointState::ALL.iter().map(|s| s.sym()).collect()
    }

    /// The directional drive this joint state contributes to the figure's motion when a frame
    /// resolves: `+1` forward (toward the opponent), `-1` backward, `0` neutral. `Hold` is `0`
    /// drive but braces (see [`JointState::braces`]).
    pub fn drive(self) -> i32 {
        match self {
            JointState::Contract => 1,
            JointState::Extend => -1,
            JointState::Relax | JointState::Hold => 0,
        }
    }

    /// Whether this joint state BRACES — resists being pushed. A braced joint cancels one unit of an
    /// opposing figure's forward drive (a defensive lock). Only `Hold` braces.
    pub fn braces(self) -> bool {
        matches!(self, JointState::Hold)
    }
}

/// A figure's full joint pose — the value of all [`N_JOINTS`] joints. A move IS a `JointVector`
/// (plus a blinding nonce); the figure cell stores it across [`N_JOINTS`] `sym` slots.
pub type JointVector = [JointState; N_JOINTS];

/// The all-`Relax` rest pose — the figure's neutral starting stance.
pub const REST_POSE: JointVector = [JointState::Relax; N_JOINTS];

// ---------------------------------------------------------------------------
// Figure — a dregg cell whose `sym` slots are its joints
// ---------------------------------------------------------------------------

/// Slot layout inside a figure cell's 16 user fields. The first [`N_JOINTS`] slots are the joint
/// `sym` slots (the enum-pinned ones); the trailing slots carry the figure's scalar position and
/// score (kept as the executor's `u64` lane). All within the 16 user slots
/// ([`dregg_cell::FieldElement`] array).
pub mod slot {
    use super::N_JOINTS;
    /// The first joint slot; joints occupy `JOINT_BASE .. JOINT_BASE + N_JOINTS`.
    pub const JOINT_BASE: usize = 0;
    /// The figure's 1-D position along the strip (a scalar `u64` lane). Distinct from the joint
    /// `sym` slots so a position read never collides with a joint enum.
    pub const POSITION: usize = N_JOINTS; // slot 4
    /// The figure's running score (a scalar `u64` lane mirroring the verified-ledger score column).
    pub const SCORE: usize = N_JOINTS + 1; // slot 5
}

/// A **figure** — one fighter, modeled as a dregg cell. Its joints are the first [`N_JOINTS`] `sym`
/// slots of [`Figure::cell`]; its 1-D position and running score are scalar slots. The figure's id
/// is the cell id the verified ledger and the move commitments bind to.
///
/// The figure cell carries a real [`CellProgram`] ([`Figure::joint_program`]) that pins every joint
/// slot to the [`JointState`] enum via [`StateConstraint::SymMemberOf`] — so a pose that drives a
/// joint out of the enum is refused by the SAME [`CellProgram::evaluate`] the executor runs.
#[derive(Clone, Debug)]
pub struct Figure {
    /// The figure's cell id (its ledger account + the cap a move binds to).
    pub id: FigureId,
    /// The figure's cell state — joints in `sym` slots, position + score in scalar slots.
    pub cell: CellState,
}

impl Figure {
    /// Spawn a figure at `position` along the strip, in the [`REST_POSE`], with zero score. The
    /// joint `sym` slots are initialised to `Relax` (the enum's `0` case).
    pub fn spawn(id: FigureId, position: i64) -> Self {
        let mut cell = CellState::new(0);
        // All joints start at Relax (sym 0) — already the zero field, but write through the
        // enum-pinned setter to keep the invariant explicit.
        for j in 0..N_JOINTS {
            cell.set_field(slot::JOINT_BASE + j, field_from_u64(JointState::Relax.sym()));
        }
        cell.set_field(slot::POSITION, field_from_u64(position as u64));
        cell.set_field(slot::SCORE, field_from_u64(0));
        Figure { id, cell }
    }

    /// The figure's **joint-state-enum cell program** — the REAL [`CellProgram`] that pins every
    /// joint slot to the [`JointState`] enum. It is `Predicate([SymMemberOf{slot_j, enum_set} ; j])`
    /// — one typed `sym` atom per joint slot. This is the Rust image of the Lean `Pred.symMemberOf`
    /// (`metatheory/Dregg2/Exec/PredAlgebra.lean`): every joint reads as a `Value.sym` whose
    /// identity is one of the enum cases. [`CellProgram::evaluate`] runs it — the exact gate the
    /// executor enforces.
    pub fn joint_program() -> CellProgram {
        let set = JointState::enum_set();
        let constraints = (0..N_JOINTS)
            .map(|j| StateConstraint::SymMemberOf {
                index: (slot::JOINT_BASE + j) as u8,
                set: set.clone(),
            })
            .collect();
        CellProgram::Predicate(constraints)
    }

    /// Read the figure's current joint pose out of its `sym` slots. Each slot is decoded back to a
    /// [`JointState`] via [`JointState::from_sym`] over the `u64` identity lane; an out-of-enum slot
    /// (which the cell program forbids) decodes to `Relax` defensively.
    pub fn pose(&self) -> JointVector {
        let mut v = REST_POSE;
        for j in 0..N_JOINTS {
            let sym = field_to_u64(&self.cell.fields[slot::JOINT_BASE + j]);
            v[j] = JointState::from_sym(sym).unwrap_or(JointState::Relax);
        }
        v
    }

    /// The figure's 1-D position along the strip.
    pub fn position(&self) -> i64 {
        field_to_u64(&self.cell.fields[slot::POSITION]) as i64
    }

    /// The figure's running score (the scalar mirror of its verified-ledger score column). `i128`
    /// to match the verified ledger's amount domain.
    pub fn score(&self) -> i128 {
        field_to_u64(&self.cell.fields[slot::SCORE]) as i128
    }

    /// **Pose the figure** — drive its joints to `joints`, GATED by the joint-state-enum cell
    /// program. Builds the candidate next cell state (joints written into their `sym` slots), then
    /// runs the REAL [`CellProgram::evaluate`] ([`Figure::joint_program`]) over the `(old, new)`
    /// transition. The pose commits IFF every joint slot reads as one of the [`JointState`] enum
    /// cases (the [`StateConstraint::SymMemberOf`] tooth); an out-of-enum drive is refused in-band
    /// with [`TussleError::IllegalJoint`].
    ///
    /// This is the executable witness that a joint slot's value is one of the enum states — the
    /// freshly-landed typed `sym`/dig atom rung, enforced by the same evaluator the executor uses.
    pub fn pose_checked(&mut self, joints: &JointVector) -> Result<(), TussleError> {
        let old = self.cell.clone();
        let mut new = self.cell.clone();
        for j in 0..N_JOINTS {
            new.set_field(slot::JOINT_BASE + j, field_from_u64(joints[j].sym()));
        }
        // THE TYPED-sym TOOTH: the figure's joint program must admit the new pose. Refused in-band
        // for any out-of-enum joint slot.
        Figure::joint_program()
            .evaluate(&new, Some(&old), None)
            .map_err(|e| TussleError::IllegalJoint(e.to_string()))?;
        self.cell = new;
        Ok(())
    }

    /// Apply a raw (already enum-validated) pose to the figure's joint slots WITHOUT re-running the
    /// gate. Used by the resolver after a reveal has passed both the fog-of-war and the enum teeth.
    fn write_pose(&mut self, joints: &JointVector) {
        for j in 0..N_JOINTS {
            self.cell
                .set_field(slot::JOINT_BASE + j, field_from_u64(joints[j].sym()));
        }
    }

    /// Set the figure's position slot (after a resolution step).
    fn write_position(&mut self, pos: i64) {
        self.cell.set_field(slot::POSITION, field_from_u64(pos as u64));
    }

    /// Set the figure's score slot to mirror its verified-ledger score column (after a joint turn).
    /// The verified ledger's amount domain is `i128`; the figure cell stores the `u64` lane of it.
    fn write_score(&mut self, score: i128) {
        self.cell.set_field(slot::SCORE, field_from_u64(score as u64));
    }
}

/// Decode the `u64` identity lane of a field (the low 8 bytes, big-endian) — the inverse of
/// [`dregg_cell::field_from_u64`], matching the executor's `field_to_u64`. Private helper.
fn field_to_u64(field: &FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes)
}

// ---------------------------------------------------------------------------
// MoveCommit — the sealed joint-vector (fog-of-war)
// ---------------------------------------------------------------------------

/// A **sealed move** — a player's chosen [`JointVector`] for the figure `figure`, blinded by a
/// secret `nonce`. The `joints` and `nonce` are SECRET until reveal; only [`MoveCommit::seal`] is
/// public during the commit phase. The same commit-reveal construction the sealed-auction app uses:
/// the seal HIDES the joints and BINDS the player to exactly one move + one figure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MoveCommit {
    /// The figure this move poses — the CAP the move binds to. A reveal against a different figure
    /// than the one it targets in this frame is refused ([`TussleError::WrongFigure`]).
    pub figure: FigureId,
    /// The chosen joint pose — secret until reveal.
    pub joints: JointVector,
    /// The blinding nonce — secret; gives the commitment hiding even over the small joint space.
    pub nonce: u64,
}

impl MoveCommit {
    /// Construct a sealed move (in the clear; call [`MoveCommit::seal`] for the public commitment).
    pub fn new(figure: FigureId, joints: JointVector, nonce: u64) -> Self {
        MoveCommit {
            figure,
            joints,
            nonce,
        }
    }

    /// The **sealed commitment** of this move — `BLAKE3(figure || joints || nonce)`. Binding (under
    /// collision-resistance a commitment opens to exactly its move) and hiding (the nonce blinds the
    /// small joint space). The fog-of-war seal: an opponent sees only this 32-byte digest during the
    /// commit phase, from which the joints are unreadable. The same construction as the sealed
    /// auction's `Bid::seal`.
    pub fn seal(&self) -> MoveSeal {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-tussle move-commit v1");
        hasher.update(&[self.figure]);
        for j in &self.joints {
            hasher.update(&j.sym().to_le_bytes());
        }
        hasher.update(&self.nonce.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors from the TUSSLE frame / match protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TussleError {
    /// A commit was attempted outside the commit phase (fail-closed: no late move-commitments).
    NotCommitPhase,
    /// A reveal/resolve was attempted while still committing (no reveal before the commit closes) —
    /// the STATE half of the cap∧state gate.
    NotRevealPhase,
    /// The frame is already resolved (terminal for this frame).
    AlreadyResolved,
    /// A reveal's seal is not among this frame's committed seals — a player who did not commit, or a
    /// peeker who changed their move so the seal no longer matches (the fog-of-war binding tooth).
    NotCommitted,
    /// A reveal poses a figure that is not the figure its commit was bound to — a player trying to
    /// move the OPPONENT'S figure (the CAP half of the cap∧state gate).
    WrongFigure { revealed: FigureId, bound: FigureId },
    /// A revealed pose drives a joint OUT of the [`JointState`] enum — refused by the figure's
    /// joint-state-enum cell program (the typed `sym` atom tooth). Carries the evaluator's reason.
    IllegalJoint(String),
    /// Both players must reveal before the frame can resolve.
    MissingReveal,
    /// The joint turn (the score-delta ring) was rejected by the verified executor — the contact
    /// move could not settle. Carries the verified executor's reason.
    JointTurnRejected(VerifiedSettleError),
}

impl std::fmt::Display for TussleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotCommitPhase => write!(f, "move-commit attempted outside the commit phase"),
            Self::NotRevealPhase => {
                write!(f, "reveal/resolve attempted before the commit phase closed")
            }
            Self::AlreadyResolved => write!(f, "this frame is already resolved"),
            Self::NotCommitted => write!(f, "the revealed move was not among the committed seals"),
            Self::WrongFigure { revealed, bound } => write!(
                f,
                "reveal poses figure {revealed} but its commit was bound to figure {bound} \
                 (a player cannot set the opponent's joints)"
            ),
            Self::IllegalJoint(reason) => {
                write!(f, "revealed pose drives a joint out of the enum: {reason}")
            }
            Self::MissingReveal => write!(f, "both players must reveal before the frame resolves"),
            Self::JointTurnRejected(e) => {
                write!(f, "the frame's joint turn was rejected by the verified executor: {e}")
            }
        }
    }
}

impl std::error::Error for TussleError {}

// ---------------------------------------------------------------------------
// Frame — the commit → reveal → resolve state machine (one joint turn)
// ---------------------------------------------------------------------------

/// The phase of a frame. Reveals bind only in `Reveal`; the resolution fires only in `Reveal`;
/// `Resolved` is terminal. The `Commit → Reveal → Resolved` ordering is the protocol's phase gate
/// (the STATE half of cap∧state), not a comment: it makes "no reveal before the commit phase closes"
/// enforced. The same shape as the sealed-auction `Phase`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FramePhase {
    /// Collecting sealed move-commitments (one per player); reveals are rejected.
    Commit,
    /// Commit phase closed; reveals accepted, the resolution may fire once both have revealed.
    Reveal,
    /// The frame has resolved (its joint turn ran); terminal.
    Resolved,
}

/// One **frame** of a match — the unit of play, and the unit of a **2-party joint turn**. Both
/// players SEAL their figure's next pose (commit, fog-of-war), both REVEAL, then a DETERMINISTIC
/// resolution runs: the joints drive the figures, contact is detected, and the contact score deltas
/// fold through the verified executor as a ring of legs. A figure's joints are set in this 2-party
/// joint turn.
#[derive(Clone, Debug)]
pub struct Frame {
    /// The two figures' ids, in `(p0, p1)` order. A reveal must pose one of these, and the one its
    /// commit was bound to (the cap tooth).
    pub players: (FigureId, FigureId),
    /// The sealed move-commitments collected during the commit phase, keyed by figure so each player
    /// commits at most once and the reveal can check the figure binding.
    commitments: BTreeMap<FigureId, MoveSeal>,
    /// The current phase.
    pub phase: FramePhase,
    /// The validly-revealed moves (collected during the reveal phase), keyed by figure.
    reveals: BTreeMap<FigureId, MoveCommit>,
}

impl Frame {
    /// Open a fresh frame between `p0` and `p1`, in the commit phase.
    pub fn new(p0: FigureId, p1: FigureId) -> Self {
        Frame {
            players: (p0, p1),
            commitments: BTreeMap::new(),
            phase: FramePhase::Commit,
            reveals: BTreeMap::new(),
        }
    }

    /// Whether `figure` is one of this frame's two players.
    fn is_player(&self, figure: FigureId) -> bool {
        figure == self.players.0 || figure == self.players.1
    }

    /// **Commit phase** — submit a sealed move-commitment for a player's figure. Legal ONLY in the
    /// commit phase (fail-closed: no late commitments). The seal HIDES the joints; an opponent sees
    /// only this digest. Mirrors the sealed-auction `Auction::commit`.
    pub fn commit(&mut self, figure: FigureId, seal: MoveSeal) -> Result<(), TussleError> {
        if self.phase != FramePhase::Commit {
            return Err(TussleError::NotCommitPhase);
        }
        if !self.is_player(figure) {
            // A non-player cannot inject a commitment into this frame.
            return Err(TussleError::WrongFigure {
                revealed: figure,
                bound: self.players.0,
            });
        }
        self.commitments.insert(figure, seal);
        Ok(())
    }

    /// Close the commit phase, opening reveals (`Commit → Reveal`). Mirrors the auction's
    /// `seal_commit_phase`.
    pub fn seal_commit_phase(&mut self) {
        if self.phase == FramePhase::Commit {
            self.phase = FramePhase::Reveal;
        }
    }

    /// **The fog-of-war tooth** — is the opponent's move readable from the public frame? It is NOT:
    /// the only public datum about `opponent`'s move during the commit/reveal-before-their-reveal
    /// window is its [`MoveSeal`], a BLAKE3 digest from which the [`JointVector`] is computationally
    /// unrecoverable. Returns the opponent's sealed digest if present — the thing a peeker sees, and
    /// all they see. (The companion `src/tests.rs` proves no joint vector is recoverable from it: the
    /// seal of a different guess does not match.)
    pub fn opponent_move_is_sealed(&self, me: FigureId) -> Option<MoveSeal> {
        let opp = if me == self.players.0 {
            self.players.1
        } else {
            self.players.0
        };
        // We can only ever observe the SEAL — never the joints. If the opponent has already revealed
        // (their own choice), that's their move on the table; before that, this digest is all there is.
        if self.reveals.contains_key(&opp) {
            None // they chose to reveal; no longer fog
        } else {
            self.commitments.get(&opp).copied()
        }
    }

    /// **Reveal phase** — open a player's move. Accepted IFF three teeth pass:
    ///   1. PHASE (state-gate): the frame is in the reveal phase (a reveal while committing is
    ///      [`TussleError::NotRevealPhase`]);
    ///   2. BINDING (fog-of-war): the move's seal is among this frame's commitments (a non-committed
    ///      or peek-then-switch move is [`TussleError::NotCommitted`]);
    ///   3. FIGURE (cap-gate): the move poses the SAME figure its commitment was filed under (a
    ///      player posing the opponent's figure is [`TussleError::WrongFigure`]).
    ///
    /// On all three passing, the figure's joint-state-enum program is checked ([`Figure::pose_checked`]
    /// happens at resolution; here we additionally verify the revealed pose is enum-valid so an
    /// out-of-enum move is rejected at reveal, [`TussleError::IllegalJoint`]). The move joins the
    /// revealed set.
    pub fn reveal(&mut self, mv: MoveCommit) -> Result<(), TussleError> {
        match self.phase {
            FramePhase::Commit => return Err(TussleError::NotRevealPhase),
            FramePhase::Resolved => return Err(TussleError::AlreadyResolved),
            FramePhase::Reveal => {}
        }
        // CAP tooth: the move must pose one of this frame's figures, and the figure it was committed
        // under. We look up the commitment by the figure the move CLAIMS to pose.
        let seal = mv.seal();
        let bound = match self.commitments.get(&mv.figure) {
            Some(s) => *s,
            // No commitment under this figure: either a non-player or a move whose figure is not the
            // one it committed as — both refused (a peeker who re-targets, or the opponent's figure).
            None => {
                // If the seal matches some OTHER committed figure, that is a wrong-figure attempt.
                if let Some((&bound_fig, _)) =
                    self.commitments.iter().find(|(_, s)| **s == seal)
                {
                    return Err(TussleError::WrongFigure {
                        revealed: mv.figure,
                        bound: bound_fig,
                    });
                }
                return Err(TussleError::NotCommitted);
            }
        };
        // BINDING tooth: the seal must match the commitment filed under this figure.
        if seal != bound {
            return Err(TussleError::NotCommitted);
        }
        // ENUM tooth: the revealed pose must be enum-valid (the typed `sym` atom). We check it here
        // against a throwaway figure so an illegal joint is refused at reveal.
        let mut probe = Figure::spawn(mv.figure, 0);
        probe.pose_checked(&mv.joints)?;
        self.reveals.insert(mv.figure, mv);
        Ok(())
    }

    /// Whether both players have validly revealed (the resolution can fire).
    pub fn both_revealed(&self) -> bool {
        self.reveals.contains_key(&self.players.0) && self.reveals.contains_key(&self.players.1)
    }

    /// The revealed move for a player, if any (after a valid [`Frame::reveal`]).
    pub fn revealed(&self, figure: FigureId) -> Option<&MoveCommit> {
        self.reveals.get(&figure)
    }

    /// **Resolve the frame — the 2-party joint turn.** Requires both players to have revealed.
    /// Runs the DETERMINISTIC resolution ([`resolution::resolve_contact`]) over the two revealed
    /// joint vectors and the figures' current positions, producing the position deltas, the contact
    /// (if any), and the score deltas. The score deltas are emitted as a balanced **ring of legs**
    /// and folded through the VERIFIED per-asset executor
    /// ([`dregg_intent::verified_settle::settle_ring_verified`]) — the 2-party joint turn over the
    /// two figure cells' score columns. On success it:
    ///   - writes both figures' new joint poses (now enum-validated and committed),
    ///   - writes both figures' new positions,
    ///   - returns the verified post-ledger + the [`FrameResolution`], and marks the frame
    ///     `Resolved`.
    ///
    /// Fails (leaving the ledger untouched — atomicity) if a player did not reveal
    /// ([`TussleError::MissingReveal`]) or the score-delta ring is rejected by the verified executor
    /// ([`TussleError::JointTurnRejected`]).
    ///
    /// This is the executable witness that a frame's score move IS a verified, conserving executor
    /// turn — the contact resolution emits ring legs, and the verified fold (the Lean
    /// `Ring.settleRing`) applies them atomically and conservingly, cross-checked leg-by-leg against
    /// the real Lean executor export on a native build.
    pub fn resolve(
        &mut self,
        f0: &mut Figure,
        f1: &mut Figure,
        ledger: &VerifiedLedger,
    ) -> Result<(VerifiedLedger, FrameResolution), TussleError> {
        if self.phase != FramePhase::Reveal {
            return Err(TussleError::NotRevealPhase);
        }
        if !self.both_revealed() {
            return Err(TussleError::MissingReveal);
        }
        // The two revealed moves, in player order. Defensive: both keys are present (both_revealed).
        let m0 = *self.reveals.get(&self.players.0).ok_or(TussleError::MissingReveal)?;
        let m1 = *self.reveals.get(&self.players.1).ok_or(TussleError::MissingReveal)?;

        // THE DETERMINISTIC RESOLUTION — a pure function over the revealed joint vectors + positions.
        let outcome = resolution::resolve_contact(
            (f0.id, f0.position(), &m0.joints),
            (f1.id, f1.position(), &m1.joints),
        );

        // THE 2-PARTY JOINT TURN: fold the contact score deltas through the verified executor as a
        // balanced ring. An empty ring (no contact) is a no-op fold that still conserves.
        let post = settle_ring_verified(ledger, &outcome.score_legs)
            .map_err(TussleError::JointTurnRejected)?;

        // Commit the resolution to the figure cells: enum-validated joint poses + new positions +
        // the score mirror (read back from the verified post-ledger).
        f0.write_pose(&m0.joints);
        f1.write_pose(&m1.joints);
        f0.write_position(outcome.new_positions.0);
        f1.write_position(outcome.new_positions.1);
        f0.write_score(post.get(f0.id, &SCORE_ASSET));
        f1.write_score(post.get(f1.id, &SCORE_ASSET));

        self.phase = FramePhase::Resolved;
        Ok((post, outcome))
    }
}

// ---------------------------------------------------------------------------
// Match — a sequence of frames + the running score
// ---------------------------------------------------------------------------

/// The reason a match ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MatchEnd {
    /// A figure reached the target score (a knockout). Carries the winner's id.
    TargetReached(FigureId),
    /// The frame cap was hit; the higher score wins (or a draw if tied). `Some(id)` = winner,
    /// `None` = draw.
    FrameCap(Option<FigureId>),
}

/// The log of one resolved frame in a match — the commit→reveal→resolve story for replay/printing.
#[derive(Clone, Debug)]
pub struct FrameLog {
    /// The frame index (0-based).
    pub frame: usize,
    /// The two revealed poses, in player order.
    pub poses: (JointVector, JointVector),
    /// The deterministic resolution outcome (positions, contact, score legs).
    pub resolution: FrameResolution,
    /// The running scores after this frame, in player order (read from the verified ledger).
    pub scores: (i128, i128),
}

/// A **TUSSLE match** — two figures, a verified score ledger, and a sequence of frames played to a
/// target score or a frame cap. The match state advances ONLY through [`Frame::resolve`] (a verified
/// 2-party joint turn per frame), so the entire match's scoring is a chain of verified, conserving
/// executor turns.
#[derive(Clone, Debug)]
pub struct Match {
    /// Player 0.
    pub f0: Figure,
    /// Player 1.
    pub f1: Figure,
    /// The verified score ledger (the `SCORE_ASSET` column of the two figure cells, conserved each
    /// frame). Both figures are live accounts.
    pub ledger: VerifiedLedger,
    /// The target score that ends the match (a knockout). `i128` to match the verified ledger.
    pub target: i128,
    /// The frame cap (a match ends at this many frames even with no knockout).
    pub frame_cap: usize,
    /// The resolved-frame log.
    pub log: Vec<FrameLog>,
}

impl Match {
    /// Open a fresh match between two figures spawned at `±start` along the strip, with a verified
    /// score ledger seeded from a fixed bank so each figure can RECEIVE points (the verified
    /// executor moves points from a neutral bank cell into the scorer — a balanced, conserving
    /// transfer). The bank holds enough to award up to `target` points to each figure.
    pub fn new(p0: FigureId, p1: FigureId, start: i64, target: i128, frame_cap: usize) -> Self {
        let f0 = Figure::spawn(p0, -start);
        let f1 = Figure::spawn(p1, start);
        // The verified score ledger: a neutral BANK funds the points; the two figures start at 0 and
        // receive points as contacts land. Every cell a leg touches must be a live account.
        let mut ledger = VerifiedLedger::new();
        ledger.add_account(p0);
        ledger.add_account(p1);
        ledger.add_account(resolution::SCORE_BANK);
        ledger.set(p0, &SCORE_ASSET, 0);
        ledger.set(p1, &SCORE_ASSET, 0);
        // Bank funds 2× the target so either figure can be awarded up to `target` points.
        ledger.set(resolution::SCORE_BANK, &SCORE_ASSET, target.max(1) * 2 + 2);
        Match {
            f0,
            f1,
            ledger,
            target,
            frame_cap,
            log: Vec::new(),
        }
    }

    /// The running score of player 0 (read from the verified ledger).
    pub fn score0(&self) -> i128 {
        self.ledger.get(self.f0.id, &SCORE_ASSET)
    }

    /// The running score of player 1 (read from the verified ledger).
    pub fn score1(&self) -> i128 {
        self.ledger.get(self.f1.id, &SCORE_ASSET)
    }

    /// Whether the match has ended, and how. `None` = still going. A figure at or above `target`
    /// is a knockout; otherwise the match runs until [`Match::frame_cap`] frames.
    pub fn outcome(&self) -> Option<MatchEnd> {
        if self.score0() >= self.target && self.score0() >= self.score1() {
            return Some(MatchEnd::TargetReached(self.f0.id));
        }
        if self.score1() >= self.target {
            return Some(MatchEnd::TargetReached(self.f1.id));
        }
        if self.log.len() >= self.frame_cap {
            let winner = match self.score0().cmp(&self.score1()) {
                std::cmp::Ordering::Greater => Some(self.f0.id),
                std::cmp::Ordering::Less => Some(self.f1.id),
                std::cmp::Ordering::Equal => None,
            };
            return Some(MatchEnd::FrameCap(winner));
        }
        None
    }

    /// **Play one frame** from two already-chosen sealed moves — the full commit→reveal→resolve
    /// joint turn, driving the match state forward. Both moves are committed (sealed), the commit
    /// phase closes, both reveal (passing the fog-of-war + cap + enum teeth), and the frame resolves
    /// through the verified executor. Appends a [`FrameLog`] and updates the verified `ledger`.
    ///
    /// Returns the [`FrameResolution`] (the deterministic outcome). The two `MoveCommit`s must pose
    /// the match's two figures (`f0.id`, `f1.id`); a mismatched figure is refused by the cap tooth.
    pub fn play_frame(
        &mut self,
        m0: MoveCommit,
        m1: MoveCommit,
    ) -> Result<FrameResolution, TussleError> {
        let mut frame = Frame::new(self.f0.id, self.f1.id);
        // COMMIT phase — both players seal their move (the opponent sees only the digest).
        frame.commit(m0.figure, m0.seal())?;
        frame.commit(m1.figure, m1.seal())?;
        // Close commits → reveal phase.
        frame.seal_commit_phase();
        // REVEAL phase — both open (each passes the three teeth).
        frame.reveal(m0)?;
        frame.reveal(m1)?;
        // RESOLVE — the verified 2-party joint turn.
        let (post, resolution) = frame.resolve(&mut self.f0, &mut self.f1, &self.ledger)?;
        self.ledger = post;
        let frame_idx = self.log.len();
        self.log.push(FrameLog {
            frame: frame_idx,
            poses: (m0.joints, m1.joints),
            resolution: resolution.clone(),
            scores: (self.score0(), self.score1()),
        });
        Ok(resolution)
    }
}

#[cfg(test)]
mod tests;
