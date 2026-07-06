//! # `spween-dregg` — the narrative core of on-chain interactive fiction
//!
//! Binds [spween](https://docs.rs/spween) — a Twine/Ink-class narrative-choice DSL —
//! to a dregg **world-cell**, so a spween story runs verifiably on the substrate:
//! each choice is a cap-bounded, receipted **turn**, and the playthrough is an
//! **un-retconnable receipt chain**. spween deliberately externalized ALL world state
//! behind one trait ([`spween::EffectHandler`]); this crate is the dregg backend
//! behind that seam — persistent, unforgeable, un-rewritable, and *collectively
//! decidable*.
//!
//! The design is [`docs/deos/SPWEEN-ON-DREGG.md`]; this crate builds ranked steps 1–3:
//!
//! * **The `WorldCell` binding** ([`WorldCell`]) — a story is a cell holding the
//!   narrative vars; spween's `EffectHandler` is implemented over it, and advancing
//!   the story ([`WorldCell::apply_choice`]) is ONE verified turn that the real
//!   executor admits IFF the choice's gate passes. Nobody can forge a move or take a
//!   choice they are not eligible for.
//! * **Single-player verifiable CYOA** ([`Driver`]) — the STOCK [`spween::Runtime`]
//!   over a cell-backed handler; each `select_choice` is a real turn and the
//!   playthrough re-verifies ([`verify`]).
//! * **The spween→cell compiler v0** ([`compile_scene`]) — lowers a [`spween::Scene`]
//!   into a world-cell descriptor whose passages/vars are cell state and whose
//!   choice-conditions are executor-enforced [`CellProgram`](dregg_app_framework::CellProgram)
//!   predicates.
//! * **Collective CYOA** ([`run_collective`]) — the vote-driven branch loop over a
//!   [`VoteEngine`]: the audience polls each branch, the winner fires as a turn, the
//!   crowd collectively authors the story.
//!
//! ## The teeth (see `tests/`)
//!
//! * a story runs end-to-end and the playthrough re-verifies;
//! * a tampered / forged playthrough is REFUSED (a receipt-chain break, or a forged
//!   choice-turn refused by the executor on replay);
//! * a condition-gated choice is UNAVAILABLE when its gate fails — enforced as a
//!   cell-program predicate the executor re-checks (you cannot pick a choice you are
//!   not eligible for);
//! * the collective mode resolves a branch by vote.

mod collective;
mod compiler;
mod encoding;
mod real_engine;
mod verify;
mod vote;
mod world;

pub use collective::{Ballot, CollectiveError, CollectiveRound, PollContext, run_collective};
pub use compiler::{
    CompileError, CompiledStory, GENESIS_METHOD, PASSAGE_ENDED, PASSAGE_SLOT, choice_method,
    compile_scene, value_to_field,
};
pub use encoding::{field_to_u64, value_to_u64};
pub use real_engine::CollectiveChoiceEngine;
pub use verify::{StepPos, VerifyBreak, verify, verify_by_replay, verify_chain_linkage};
pub use vote::{StubVoteEngine, VoteEngine, VoteError, VoteOption, labeled_tally};
pub use world::{CellHandler, ChoiceView, Driver, Playthrough, StepReceipt, WorldCell, WorldError};

// Re-export the pieces of spween a consumer needs to parse + describe a story.
pub use spween::{Scene, Value, parse};
