//! Twin (executable model) of the io_uring provided-buffer **borrow↔recycle
//! cross-thread handoff** — the one elevated-severity reactor corner flagged as
//! gap F in `docs/engine/review/URING-REFINEMENT-SCOPE.md`.
//!
//! The model itself lives in `tests/loom.rs`, exercised under `--cfg loom` for
//! exhaustive schedule exploration. This crate is deliberately zero-dependency
//! and separate from `dataplane`: the dataplane package's `build.rs` links the
//! Lean runtime (`libleanshared`) into every target, and that runtime breaks
//! loom's unwind-based panic capture inside its stackful coroutines — the same
//! reason `ring-twin` and `wake-twin` are their own crates.
//!
//! See `tests/loom.rs` for the model, the real-handoff correspondence, and the
//! explicit statement of what it covers versus the deployed `uring.rs`.
#![deny(unsafe_op_in_unsafe_fn)]
