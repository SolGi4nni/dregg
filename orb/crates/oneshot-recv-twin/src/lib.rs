//! Twin (executable model) of the **DEPLOYED one-shot buffer-select recv path** —
//! the per-request lease `acquire -> process -> recycle` cycle through the single
//! `Conn.leased_bid` cell (`crates/dataplane/src/uring.rs`).
//!
//! This is the REAL deployed path, not a prospective one. `multishot-twin`
//! correctly flagged that the deployed recv is one-shot: `recv_br_sqe`
//! (uring.rs:757) builds a plain buffer-select `Recv` with NO multishot flag, so
//! exactly one CQE lands per SQE and the shard re-arms the NEXT recv explicitly —
//! and only after the current request's response has recycled its lease
//! (`finish_send` -> `dispatch_acc` -> `arm_recv`, uring.rs:2448/789). That
//! one-recv-in-flight-per-connection serialization is precisely what keeps the
//! single `Conn.leased_bid: Option<u16>` cell from ever holding two live leases —
//! the invariant this twin exercises, and the one `borrow-recycle-twin` (a single
//! lease, no per-request cycle) does not.
//!
//! The model itself lives in `tests/loom.rs`, exercised under `--cfg loom` for
//! exhaustive schedule exploration. This crate is deliberately zero-dependency
//! and separate from `dataplane`: the dataplane package's `build.rs` links the
//! Lean runtime (`libleanshared`) into every target, and that runtime breaks
//! loom's unwind-based panic capture inside its stackful coroutines — the same
//! reason `ring-twin`, `wake-twin`, `borrow-recycle-twin`, `splitsend-twin`,
//! `conn-limit-twin`, and `multishot-twin` are their own crates.
//!
//! See `tests/loom.rs` for the model, the real-path correspondence, and the
//! explicit statement of what it covers versus the deployed `uring.rs`.
#![deny(unsafe_op_in_unsafe_fn)]
