//! Starbridge v2 — the native dregg master interface (library core).
//!
//! The headless, gpui-free heart lives here so it is `cargo test`-able and
//! reusable by both builds:
//!   * [`world`] — the embedded verified executor + live local dregg world.
//!   * [`dynamics`] — the observation/event stream of state transitions.
//!   * [`reflect`] — the uniform reflective object model the views consume.
//!
//! The `native-full` binary (`src/main.rs`) wires these into the gpui cockpit.
//! The wire-contract client (`client`/`model`) lives in the binary crate for
//! the remote-node + `sel4-thin` paths.

#[cfg(feature = "embedded-executor")]
pub mod cipherclerk;
#[cfg(feature = "embedded-executor")]
pub mod debug;
#[cfg(feature = "embedded-executor")]
pub mod dynamics;
#[cfg(feature = "embedded-executor")]
pub mod edit;
#[cfg(feature = "embedded-executor")]
pub mod palette;
#[cfg(feature = "embedded-executor")]
pub mod reflect;
#[cfg(feature = "embedded-executor")]
pub mod replay;
#[cfg(feature = "embedded-executor")]
pub mod world;

#[cfg(feature = "embedded-executor")]
pub use world::{CommitOutcome, World};
