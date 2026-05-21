//! Federation simulation helpers.
//!
//! Provides utilities for spawning in-process federations and driving them through
//! consensus rounds, revocations, and state queries without real networking.

pub use crate::harness::{SimClock, SimFederation, SimulationHarness};

/// Create a quick single-federation harness for the common 4-node case.
pub fn quick_federation() -> SimulationHarness {
    SimulationHarness::new_federation(4)
}

/// Create a harness with two federations (3 nodes each) for cross-federation tests.
pub fn dual_federation() -> SimulationHarness {
    SimulationHarness::two_federations(3, 3)
}

/// Drive a federation through multiple consensus rounds until a block is finalized.
/// Returns the number of rounds it took, or None if `max_rounds` was exhausted.
pub fn drive_to_finalization(
    harness: &mut SimulationHarness,
    fed_idx: usize,
    max_rounds: usize,
) -> Option<usize> {
    for i in 1..=max_rounds {
        if harness.run_consensus_round(fed_idx) {
            return Some(i);
        }
    }
    None
}
