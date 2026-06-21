//! Standalone host harness for the render_blit weld's both-polarity proof.
//!
//! The render-PD crate is pinned to the bare `aarch64-sel4-roottask-musl` target
//! (`.cargo/config.toml` forces `build.target`), so `cargo test` cannot run on the
//! host. This harness `include!`s the REAL `src/render_blit.rs` (the exact function
//! main.rs drives on the seL4 boot path — not a copy) and runs its `#[cfg(test)]`
//! polarity tests on the host.
//!
//! Run:
//!   rustc --test host-check/render_blit_polarity.rs -o /tmp/render_blit_test \
//!     && /tmp/render_blit_test
//!
//! This proves the WELDED blit logic both polarities (genuine frame ✓, malformed
//! input ✗) against the source that ships in the image — a wire fact, not a fixture.

#[path = "../src/render_blit.rs"]
mod render_blit;
