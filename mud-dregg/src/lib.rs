//! # mud-dregg — a multiplayer MUD where the divergent player-timelines ARE the proven lattice.
//!
//! A multi-user dungeon built *substantially dreggically*: rooms are **cells**, a player command
//! is a **cap-bounded verifiable turn**, and players **fork / explore / stitch** divergent
//! timelines — with genuine conflicts **REFUSED** (Settlement Soundness), never silent
//! last-writer-wins. It composes the existing dregg substrate; it invents no new primitive.
//!
//! ## The mapping ([`docs/deos/SPWEEN-ON-DREGG.md`] §4.3)
//!
//! - **Rooms are cells.** A MUD world is a graph of room/entity cells (the `first-room`
//!   room-as-cell shape); each room holds its state (who is present, what has been said, who
//!   owns an entity) as cell state fields. See [`dungeon::Dungeon`].
//! - **Commands are verifiable turns.** `go hall`, `take sword`, `say hi` lower (through the
//!   [`dungeon::WorldCell`] seam) to the effects of ONE cap-bounded turn on a world cell. The
//!   turn re-verifies (a real `TurnReceipt`); nobody can forge another player's move (an
//!   ungranted target is a real `CapabilityNotHeld` executor refusal); the world can't be
//!   secretly rewritten (turns land on the ledger). See [`dungeon::Dungeon::issue`].
//! - **Multiplayer IS branch-stitch.** Players fork the world into divergent timelines (each a
//!   configuration of the distributed-time-travel lattice `(E, ≤, #)`), explore privately, and
//!   stitch back through the settlement-sound gate: disjoint edits merge clean, a genuine
//!   conflict (two players mutate the same entity) is a `#`-conflict **REFUSED** — surfaced as a
//!   conflict object, never a silent overwrite. This composes
//!   [`starbridge_v2::branch_stitch_session::BranchStitchSession`] (the operable shadow of
//!   `Metatheory.SettlementSoundness.settlement_soundness`, proven axiom-clean). See
//!   [`scenario::tooth_fork_explore_stitch_disjoint_merges`] and
//!   [`scenario::tooth_real_conflict_refused`].
//!
//! ## What is REAL vs modeled (honest)
//!
//! - **Real dregg, no stubs:** the rooms/players are real [`starbridge_v2::world::World`] cells;
//!   every command is a real signed turn through the real `embedded-executor`; the forged-move
//!   refusal is the executor's genuine `CapabilityNotHeld`; the fork/stitch is the real
//!   `BranchStitchSession` over a real `World` fork, and the conflict refusal is the real
//!   field-granular settlement gate (the SAME code path the branch-stitch-multiplayer flagship
//!   and the proven Lean gate drive).
//! - **Modeled:** the MUD *surface* — the [`dungeon::Command`] verbs and their lowering to
//!   `set_field` effects — is defined directly here. The [`dungeon::WorldCell`] trait is a LOCAL
//!   definition of the `spween-dregg` seam (world-state-as-cell + command→turn); in the full
//!   stack that `WorldCell` is compiled from a spween `Scene` (the passage graph → a
//!   `CellProgram`), and this crate reconciles with the real one AT REGISTRATION — a `mud-dregg`
//!   dungeon and a compiled spween world present the same surface (a `focus` cell + a `lower`).
//!
//! Run the playable arc: `cargo run --bin mud-dregg`. Verify the teeth: `cargo test`.

pub mod dungeon;
pub mod scenario;

pub use dungeon::{
    actor_tag, Command, CommandOutcome, Dungeon, Layout, WorldCell, SLOT_OWNER, SLOT_PRESENCE,
    SLOT_SAY,
};
pub use scenario::run_arc;
