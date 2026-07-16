//! # dregg-automatafl — the verified automatafl (n=2) board-transition AIR.
//!
//! A hand-authored Custom-VK circuit checking `new == apply_turn(old, moves)`
//! (`Dregg2.Games.Automatafl.applyTurn`), gated by `StateConstraint::Custom`. The
//! reference oracle (`reference`) computes the next board off-circuit; the AIR
//! (`air` + `moves`) RE-CHECKS it with low-degree DSL gates, random-access board
//! reads (one-hot dot products), and a bit-decomposition range gadget — HASH-FREE,
//! Merkle-free, Lookup-free, so it dodges every custom-leaf-adapter residual and
//! folds through `prove_custom_leaf_with_commitment` →
//! `prove_turn_chain_recursive` → `verify_history`.
//!
//! Staged: **D1** the automaton-step-only AIR; **D2** + single-move apply; **D3**
//! + the n=2 resolution. `Builder::air_accepts` shadows "the leaf proves" for the
//! fast refinement battery; the `#[ignore]` SLOW tests drive the real leaf proof +
//! recursion fold + light-client accept.

//! ## The playable surface (additive)
//!
//! [`game`] deploys the same n=2 match on a REAL [`spween_dregg::WorldCell`] (the commit → reveal →
//! resolve teeth), and [`surface`] hosts it as a [`dreggnet_offerings::Offering`]
//! ([`AutomataflOffering`]) whose board is a [`deos_view::ViewNode::CoordGrid`] with rook-line
//! legal-move highlighting and a per-viewer sealed-move fog — so automatafl plays on the web
//! catalog (and thereby Discord / Telegram / WeChat, which render the same `Surface`).

pub mod air;
pub mod builder;
pub mod game;
pub mod moves;
pub mod reference;
pub mod surface;

pub use air::{
    SealedMove, build_d1, build_d1_bound, build_d1_honest, build_d1_honest_bound, build_d2,
    build_d2_bound, build_d2_honest, build_d2_honest_bound, build_d3, build_d3_bound,
    build_d3_honest, build_d3_honest_bound, build_sealed, build_sealed_bound, build_sealed_honest,
    build_sealed_honest_bound, placeholder_roots,
};
pub use builder::Builder;
pub use game::{AutomataflGame, Deployment, MatchState};
pub use reference::{Board, Move, apply_turn, automaton_step};
pub use surface::{AutomataflOffering, AutomataflSession, Phase, Seat};
