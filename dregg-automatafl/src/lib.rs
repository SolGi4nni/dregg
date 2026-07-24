//! # dregg-automatafl — the verified automatafl board-transition, proven through Lean descriptors.
//!
//! The automatafl turn `new == apply_turn(old, moves)` (`Dregg2.Games.Automatafl.applyTurn`) folds
//! as `apply_turn = automaton_step ∘ resolve_mid` — two legs, each proven through a **PROVEN
//! Lean-emitted IR-v2 descriptor** (house-law #1: the AIR is authored in Lean, never in Rust):
//!
//! * **Leg R** (`old → mid`, move adjudication) — `automataflResolveDescN n`
//!   (`AutomataflResolveEmit.lean`), whose `cMidV4` IS `AutomataflRules.roundStep`'s resolve board.
//! * **Leg A** (`mid → new`, the automaton step) — `automataflStepDescN n`
//!   (`AutomataflStepEmit.lean`), refined against `automatonStep`.
//!
//! This crate is Rust that only (1) computes the transition OFF-circuit — [`reference`], the pure
//! game oracle + refinement target — and (2) FILLS the proven descriptor's trace and CALLS the
//! general IR-v2 prover, never authoring a constraint. The two trusted fail-closed witness
//! generators SOLVE the descriptor's OWN gates: [`resolve_witness`] (Leg R) and [`witness`] (Leg A),
//! each backed by a shape-independent layout mirror ([`resolve_layout`] / [`step_layout`]) of the
//! Lean emit. The hand-authored Rust AIR (`air`/`moves`/`builder`) is DELETED — the Lean descriptor
//! is now the SOLE authority for what the game proves. Emitted sizes: `n ∈ {2, 11}`.

//! ## The playable surface (additive)
//!
//! [`game`] deploys the same n=2 match on a REAL [`spween_dregg::WorldCell`] (the commit → reveal →
//! resolve teeth), and [`surface`] hosts it as a [`dreggnet_offerings::Offering`]
//! ([`AutomataflOffering`]) whose board is a [`deos_view::ViewNode::CoordGrid`] with rook-line
//! legal-move highlighting and a per-viewer sealed-move fog — so automatafl plays on the web
//! catalog (and thereby Discord / Telegram / WeChat, which render the same `Surface`).

pub mod game;
pub mod legc_layout;
pub mod legc_witness;
pub mod reference;
pub mod resolve_layout;
pub mod resolve_marks_layout;
pub mod resolve_marks_witness;
pub mod resolve_witness;
pub mod step_layout;
pub mod step_marks_layout;
pub mod step_marks_witness;
pub mod surface;
pub mod witness;

pub use game::{AutomataflGame, Deployment, MatchState};
pub use reference::{Board, Move, apply_turn, automaton_step};
pub use surface::{AutomataflOffering, AutomataflSession, Phase, Seat};
pub use witness::placeholder_roots;
