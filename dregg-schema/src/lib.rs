//! # `dregg-schema` — the platform keystone (a component schema + a verified allocator).
//!
//! An author declares typed **components**; the crate emits a checked slot/heap
//! **layout**, a generated **`CellProgram`**, and a typed **API** — each component
//! compiling to a proven tooth of the cell-program ISA (`cell/src/program/types.rs`).
//!
//! ```text
//!   Schema (author intent)                        docs/GAME-STRATEGY.md Phase 2
//!     │  stat / resource / identity / invariant / collection
//!     ▼
//!   allocate()  ──►  Layout (untrusted)  ──►  CheckedLayout   (Legal: disjoint + in-bounds,
//!     │                                          ▲             the RotatedLayout discipline —
//!     │  translation validation                 │             an ill-aligned layout is
//!     │  (untrusted search, CHECKED output)      │             UNCONSTRUCTABLE)
//!     ▼                                          │
//!   emit_program()  ──►  CellProgram::Cases  (genesis + move teeth)
//!     │
//!     ▼
//!   SchemaGame::deploy()  ──►  a real spween_dregg::WorldCell  (the deployed executor
//!     │                                                          re-checks the teeth)
//!     ▼
//!   .seed() / .move_().set(..).commit()   —— a verified turn chain
//! ```
//!
//! ## Refinement (translation validation)
//!
//! The emitted `CellProgram` admits EXACTLY the declared-component moves: the real
//! executor re-checks every component's tooth on the post-state, so a legal move
//! commits and an illegal one (over-cap stat, resource decrease, identity rewrite,
//! invariant violation, collection shrink) is refused. The tests
//! (`tests/refinement.rs`) drive this per archetype.
//!
//! ## Honest scope
//!
//! The Legality + refinement here are the **Rust translation-validation** forms: the
//! `Legal` check ([`layout::Layout::legal`]) is the pattern imported from
//! `metatheory/Dregg2/Circuit/Emit/RotatedLayout.lean`, and the refinement is
//! established by driven test (a legal move commits, each illegal move is refused) on
//! the real executor. The deeper **Lean-PROVEN** `Legal` obligation over this allocator
//! and the **game-turn-slice leaf** refinement (schema → allocator → CellProgram+proofs
//! → leaf → fold → verify_history) are the named follow-ups.

pub mod emit;
pub mod game;
pub mod layout;
pub mod schema;

pub use emit::{
    EmitError, GENESIS_METHOD, MOVE_METHOD, emit_program, genesis_oneshot_teeth,
    genesis_sentinel_freeze, teeth_for,
};
pub use game::{GameError, SchemaGame, Turn, check_layout, compiled_story};
pub use layout::{
    Assignment, CheckedLayout, Layout, LayoutError, LegalError, RegisterWidth, STATE_SLOTS, Slot,
    allocate, allocate_checked,
};
pub use schema::{Archetype, Component, Placement, Schema};

/// **The example keystone game** — "The Descent" state, declared via the schema.
///
/// Six components exercising all five archetypes:
/// * `hp`     — stat `0..=20`         (bounded, `FieldGte + FieldLte`)
/// * `floor`  — stat `1..=99`         (bounded — exercises the min side)
/// * `gold`   — resource              (monotone, `Monotonic`)
/// * `owner`  — identity              (write-once, `WriteOnce`)
/// * `shield` — invariant `<= hp`     (cross-field, `FieldLteOther`)
/// * `items`  — collection            (heap monotone counter, `HeapField`)
pub fn descent_schema() -> Schema {
    Schema::new("the-descent")
        .stat("hp", 0, 20)
        .stat("floor", 1, 99)
        .resource("gold")
        .identity("owner")
        .invariant("shield", "hp", 0)
        .collection("items")
}
