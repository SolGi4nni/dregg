//! Twin (executable model) of the reactor's SHARED per-source
//! **connection-limit gate** — `SharedStanding::admit` / `admit_counted` /
//! `on_close` in `crates/dataplane/src/standing.rs`.
//!
//! This model used to cover only the thread-per-connection *blocking* reactor,
//! because that was the only backend whose per-source counters were touched by
//! more than one thread: the io_uring / kqueue shards each kept a private
//! lock-free `Standing` table, one per event loop. That was itself the bug — a
//! per-shard table enforces a configured `max-connections N` once per SHARD, so
//! the shipped reactor admitted about `N * shards` per source while the proven
//! `Reactor.Stage.ConnLimit` / `Reactor/StandingCounters.lean` statement is
//! per-SOURCE over a SINGLE store (`conformance/dos/FINDING-per-shard-standing.md`).
//! Every backend now shares the one process-wide `SharedStanding`, so what this
//! model covers is the gate on the reactor that actually ships — and the race it
//! explores is no longer hypothetical for the shard path: `shards` event loops
//! accept from the same listener concurrently.
//!
//! `admit` (the blocking host, which does not count a refusal) and
//! `admit_counted` (the shard reactors, whose refusals enter the slab and so are
//! counted) differ only in that bookkeeping; both are the same
//! check-and-increment critical section, which is what this model is about.
//!
//! The safety claim (`SharedStanding::admit` / `admit_counted` doc-comments,
//! machine-checked nowhere before this model): the check-and-increment is a
//! SINGLE critical section, so
//! two concurrent accepts from one source cannot both read `active == cap-1` and
//! both admit — there is no TOCTOU window that over-admits past the cap. Split
//! that check and increment into two critical sections and the window reopens:
//! both accepts read under the cap, both increment, and the source ends with
//! `cap+1` live connections — the `ConnLimit` decision (`Reactor.Stage.ConnLimit`,
//! `Reactor/StandingCounters.lean`) is violated at run time. This is the same
//! structural invariant `SharedStanding::rate_note` relies on for the `429`
//! rate gate (one stripe held across age-and-count).
//!
//! The model itself lives in `tests/loom.rs`, exercised under `--cfg loom` for
//! exhaustive schedule exploration. This crate is deliberately zero-dependency
//! and separate from `dataplane`: the dataplane package's `build.rs` links the
//! Lean runtime (`libleanshared`) into every target, and that runtime breaks
//! loom's unwind-based panic capture inside its stackful coroutines — the same
//! reason `ring-twin`, `wake-twin`, `borrow-recycle-twin`, and `splitsend-twin`
//! are their own crates.
//!
//! See `tests/loom.rs` for the model, the real-gate correspondence, and the
//! explicit statement of what it covers versus the deployed `standing.rs`.
#![deny(unsafe_op_in_unsafe_fn)]
