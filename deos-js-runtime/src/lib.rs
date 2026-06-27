//! # deos-js-runtime — the native (pure-Rust, no-servo) deos-js engine.
//!
//! A cell can host JavaScript — event handlers / reactive logic for its surface,
//! beyond a static view-tree. `deos-js` runs that JS on real SpiderMonkey (`mozjs`),
//! the multi-GB C++ engine that is the servo/web elephant, so it runs in the web shell
//! only. This crate runs the SAME cell-JS on a **pure-Rust** engine ([`boa_engine`])
//! that builds anywhere — the gpui-native cockpit AND wasm/web — so a cell's attached
//! JS runs in the cockpit, not just servo. See `docs/deos/JS-ON-CELLS.md`.
//!
//! The architecture:
//!
//!   - [`applet`] — the **substance** (engine-independent): a [`CellApplet`] mints a
//!     cell on the embedded [`dregg_sdk::embed::DreggEngine`] and fires a named
//!     affordance as a REAL cap-gated verified turn (the `is_attenuation` cap tooth →
//!     the executor → a `TurnReceipt`). This is the SAME path `deos-js::applet` runs;
//!     binding the substrate crates directly (not `deos-js`, which would drag mozjs in)
//!     proves the substance binding is genuinely engine-independent.
//!   - [`runtime`] — the **engine**: a [`NativeRuntime`] wraps a fresh [`boa_engine`]
//!     `Context` (NO ambient host bindings — the sandbox) and installs the cap-bounded
//!     host surface. The keystone host fn is `t(turn, arg)` — fire an affordance =
//!     commit one verified turn — so cell-JS interactions ARE verified turns.

pub mod applet;
pub mod runtime;
pub mod world;

pub use applet::{Affordance, ApplyOp, CellApplet, FireError, Slot};
pub use runtime::{NativeRuntime, RunOutcome, WorldOutcome};
pub use world::{CellWorld, Fired};
