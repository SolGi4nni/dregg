//! # The `.dungeon` authoring lane — parse → validate → COMPILE onto the real substrate.
//!
//! The missing artifact of the forge→substrate migration (backlog G7): `attested-dm`
//! proved a `.dungeon` file is authorable and its parser/validator are PURE (zero
//! ledger coupling); this crate proved every dungeon mechanic lowers to a real
//! executor tooth. This module joins them — a hand-written `.dungeon` text becomes a
//! deployed [`spween_dregg::WorldCell`] whose gates are `CellProgram` constraints the
//! verified executor re-checks on every turn, with a translation-validation check
//! standing between the lowering and the deploy.
//!
//! * [`ir`] — the pure ruleset types (ported from `attested-dm`'s `game.rs`).
//! * [`parse`] — the line-oriented `.dungeon` parser (ported from
//!   `attested-dm/src/dungeon_dsl.rs`; error messages intact).
//! * [`validate`] — the semantic validator (same lints, same messages).
//! * [`compile`] — [`compile::compile_world`]: `GameWorld` → scene → `CellProgram`
//!   (+ staple-closure augmentation), CHECKED against the source before it is ever
//!   returned. See its module docs for the lowering table and the honest residual
//!   list (hostile/combat/spell/consumable/status/light/lose are refused BY NAME).

pub mod compile;
pub mod ir;
pub mod parse;
pub mod validate;

pub use compile::{
    ChoiceKind, CompileError, CompiledDungeon, DUNGEON_WON_VAR, LoweredChoice, check_lowering,
    compile_world, flag_var, item_var,
};
pub use ir::GameWorld;
pub use parse::{DungeonError, parse_dungeon, parse_world};
pub use validate::{Issue, Severity, validate};
