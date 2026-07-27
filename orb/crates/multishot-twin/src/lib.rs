//! Twin (executable model) of the io_uring **multishot-recv re-arm
//! coordination** — a reactor concurrency edge not covered by any existing
//! twin.
//!
//! ## The edge
//!
//! A multishot recv (`IORING_OP_RECV` + `IORING_RECV_MULTISHOT`, drawing its
//! landing buffers from the provided-buffer ring) is armed with ONE SQE and
//! posts MANY CQEs — each carrying a buffer id and the `F_MORE` flag while it
//! stays armed. When the ring is exhausted (a CQE with `res == -ENOBUFS`) the
//! kernel clears `F_MORE`: the multishot is now OFF and the application MUST
//! re-arm it. It can only re-arm once a provided buffer is free again — and
//! buffers become free when a serve worker *recycles* its lease. If that
//! recycle runs on the worker thread (a legitimate offload — the worker
//! republishes the slot and pokes the recv back to life), then the re-arm
//! decision RACES the recycle across threads.
//!
//! The invariant (`tests/loom.rs`): the recv is re-armed **exactly once** per
//! exhaustion once a buffer is available — never *dropped* (a lost re-arm
//! strands the connection though a buffer is free — the receive never restarts)
//! and never *double-armed* (two multishot recvs in flight on one fd
//! double-deliver bytes / double-consume the ring). Both hazards are the
//! classic two-flag rendezvous: the terminal-CQE side publishes `armed = off`,
//! the recycle side publishes `free += 1`, and whichever thread observes both
//! must claim the single re-arm.
//!
//! ## Honest scope
//!
//! This models a **prospective** multishot design. The DEPLOYED `uring.rs` recv
//! path is *one-shot*: `recv_br_sqe` (uring.rs:757) builds a plain buffer-select
//! `Recv` with NO multishot flag, `on_recv_br` (uring.rs:1975) handles one
//! completion and the shard re-arms explicitly, and `recycle_bid` (uring.rs:2157)
//! runs on the SAME shard thread — so today there is no cross-thread re-arm race
//! to explore. The F_MORE terminal-vs-more discipline this model turns on does
//! already exist in the deployed zero-copy SEND path (`on_send_zc`, `cqueue::more`,
//! uring.rs:2386). This crate is loom evidence for ONE re-arm invariant on a
//! faithful hand-model of a multishot recv path — NOT a proof that `uring.rs` is
//! verified, and NOT a claim that the current deploy contains this race.
//!
//! The model itself lives in `tests/loom.rs`, exercised under `--cfg loom` for
//! exhaustive schedule exploration. This crate is deliberately zero-dependency
//! and separate from `dataplane`: the dataplane package's `build.rs` links the
//! Lean runtime (`libleanshared`) into every target, and that runtime breaks
//! loom's unwind-based panic capture inside its stackful coroutines — the same
//! reason `ring-twin`, `wake-twin`, `borrow-recycle-twin`, `splitsend-twin`, and
//! `conn-limit-twin` are their own crates.
#![deny(unsafe_op_in_unsafe_fn)]
