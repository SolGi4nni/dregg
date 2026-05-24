//! DSL helpers used by the typestate `ActionBuilder` (see `builder.rs`).
//!
//! - [`conservation`]: derive an action's `balance_change` from its
//!   emitted effects (P2.D). This replaces the user-facing
//!   `balance_change(delta)` setter on the legacy builder.

pub mod conservation;
