//! Synchronization primitives, switched between `std` and `loom`.
//!
//! Under `--cfg loom` the atomics are the loom-instrumented versions, so the
//! model checker explores every interleaving of the reconfig-thread stores
//! against the shard-thread loads (and every C11-permitted read). Under normal
//! builds the same names resolve to `std`, so the identical model source is what
//! the stress lane exercises on real hardware.

#[cfg(loom)]
pub(crate) use loom::sync::atomic::{AtomicU32, AtomicU64, Ordering};

#[cfg(not(loom))]
pub(crate) use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
