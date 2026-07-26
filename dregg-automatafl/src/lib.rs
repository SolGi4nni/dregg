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
//! This crate is Rust that only (1) ASKS the transition of the proven Lean — [`rules`], every answer
//! computed by `@[export] dregg_automatafl_rules` over `Dregg2.Games.AutomataflRules` — and (2) FILLS
//! the proven descriptor's trace and CALLS the general IR-v2 prover, never authoring a constraint. The
//! two trusted fail-closed witness generators SOLVE the descriptor's OWN gates: [`resolve_witness`]
//! (Leg R) and [`witness`] (Leg A), each backed by a shape-independent layout mirror
//! ([`resolve_layout`] / [`step_layout`]) of the Lean emit. The hand-authored Rust AIR
//! (`air`/`moves`/`builder`) is DELETED — the Lean descriptor is now the SOLE authority for what the
//! game proves. Emitted sizes: `n ∈ {2, 11}`.
//!
//! ## ⚑ The Rust game oracle is DELETED (`src/reference.rs`)
//!
//! Until now this crate carried its own transition: `reference.rs`, a hand transcription of
//! `~/dev/automatafl/logic/src/game.rs` — one of two Rust experiments the game's author has said were
//! "always different experiments, never to be canonical". The four-way conformance audit
//! (`docs/reference/AUTOMATAFL-RULES-CONFORMANCE-AUDIT.md`) read all four artifacts against the
//! Creator-Approved ruleset and found the LEAN the only one faithful on every clause checked. Two of
//! that lineage's divergences were live in the file the witness generators consulted as their oracle:
//! a **2-cycle** SWAPPED both pieces (the ruleset keeps them PUT), and the occlusion scan skipped the
//! **destination** (so a mover DESTROYED a stationary piece the ruleset says blocks it). The first was
//! already known in-tree — `resolve_witness.rs` documented that its descriptor "deliberately diverges
//! from `reference::resolve_mid`" on exactly that input, which is to say the oracle was known not to
//! be a valid cross-check of the object it was checking.
//!
//! It is gone. [`board`] keeps the state SHAPE (and the wire that carries it), [`rules`] asks the
//! Lean, and there is no fallback: an archive without the export makes those calls fail, because the
//! alternative is answering with semantics that are known to be wrong.

//! ## The playable surface (additive)
//!
//! [`game`] deploys the same n=2 match on a REAL [`spween_dregg::WorldCell`] (the commit → reveal →
//! resolve teeth), and [`surface`] hosts it as a [`dreggnet_offerings::Offering`]
//! ([`AutomataflOffering`]) whose board is a [`deos_view::ViewNode::CoordGrid`] with rook-line
//! legal-move highlighting and a per-viewer sealed-move fog — so automatafl plays on the web
//! catalog (and thereby Discord / Telegram / WeChat, which render the same `Surface`).
//!
//! **THE PLAYED BOARD IS THE PROVEN BOARD.** The surface plays the STOCK 11×11 two-player game
//! ([`rules::stock_two_player`], four corner goals) — the emitted descriptor size — and the
//! session RECORDS every resolved round's two revealed moves ([`AutomataflSession::rounds`]). So a
//! played match is exactly the object the two-leg fold attests. It previously played an invented
//! 5×5 mini-variant and threw every move away, which left the crown with nothing but the
//! automaton-only chain at a size no descriptor is emitted for.

pub mod board;
pub mod game;
pub mod legc_layout;
pub mod legc_witness;
pub mod resolve_layout;
pub mod resolve_marks_layout;
pub mod resolve_marks_witness;
pub mod resolve_witness;
pub mod rules;
pub mod step_layout;
pub mod step_marks_layout;
pub mod step_marks_witness;
pub mod surface;
pub mod witness;

pub use board::{Board, Move};
pub use game::{AutomataflGame, Deployment, MatchState};
pub use rules::{apply_turn, automaton_step};
pub use surface::{AutomataflOffering, AutomataflSession, Phase, PlayedTurn, Seat};
pub use witness::placeholder_roots;
