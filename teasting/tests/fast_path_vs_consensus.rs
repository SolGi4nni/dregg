//! Fast-path vs consensus routing integration test.
//!
//! Pyana uses two execution paths:
//! - **Fast path (single-owner)**: A turn that only touches cells owned by the submitter
//!   can be applied immediately without consensus (local signature suffices).
//! - **Consensus path (shared cells)**: A turn touching cells owned by multiple agents
//!   requires consensus to prevent double-spend and resolve ordering.
//!
//! This test verifies that the routing logic correctly distinguishes these cases and
//! that both paths produce consistent results.

use pyana_cell::{Cell, CellId, Ledger};
use pyana_turn::executor::{ComputronCosts, TurnExecutor};
use pyana_turn::{Turn, TurnResult};
use pyana_types::PublicKey;

/// Helper: create a cell owned by the given public key.
#[allow(dead_code)]
fn make_cell(owner: &PublicKey, domain: &str) -> Cell {
    let token_id = *blake3::hash(domain.as_bytes()).as_bytes();
    Cell::new(*owner.as_bytes(), token_id)
}

/// Single-owner turn routes to fast path.
#[test]
#[ignore = "TODO: implement routing directive computation from turn + ledger state"]
fn test_single_owner_routes_to_fast_path() {
    // TODO: Steps to implement:
    // 1. Create a ledger with a cell owned by Alice.
    // 2. Create a turn that only reads/writes Alice's cell.
    // 3. Compute the routing directive.
    // 4. Assert it returns RoutingDirective::FastPath (or equivalent).
    //
    // This requires the routing module to inspect the turn's access set
    // and compare against cell ownership in the ledger.
}

/// Multi-owner turn routes to consensus.
#[test]
#[ignore = "TODO: implement routing directive computation from turn + ledger state"]
fn test_multi_owner_routes_to_consensus() {
    // TODO: Steps to implement:
    // 1. Create a ledger with cells owned by Alice and Bob.
    // 2. Create a turn that touches both Alice's and Bob's cells.
    // 3. Compute the routing directive.
    // 4. Assert it returns RoutingDirective::Consensus (or equivalent).
}

/// Fast-path execution: single-owner turn executes immediately.
#[test]
#[ignore = "TODO: implement fast-path executor that skips consensus"]
fn test_fast_path_executes_immediately() {
    // TODO: Steps to implement:
    // 1. Set up a harness with a single federation.
    // 2. Create Alice's cell in the ledger.
    // 3. Submit a single-owner turn.
    // 4. Assert it executes without running a consensus round.
    // 5. Assert the ledger state is updated.
}

/// Consensus-path execution: shared-cell turn waits for consensus.
#[test]
#[ignore = "TODO: implement consensus-gated turn execution"]
fn test_consensus_path_waits_for_finalization() {
    // TODO: Steps to implement:
    // 1. Set up a harness with a federation.
    // 2. Create cells owned by Alice and Bob.
    // 3. Submit a multi-owner turn.
    // 4. Assert it does NOT execute immediately.
    // 5. Run consensus round.
    // 6. Assert it executes after finalization.
}

/// Both paths produce the same final state for the same logical operation.
#[test]
#[ignore = "TODO: implement determinism test across execution paths"]
fn test_both_paths_deterministic() {
    // TODO: Steps to implement:
    // 1. Execute the same logical operation (e.g., transfer 100 units) twice:
    //    once via fast-path (Alice sends from her own cell),
    //    once via consensus (Alice + Bob co-sign a shared-cell operation).
    // 2. Assert both produce equivalent final states (modulo cell ownership differences).
    //
    // This is important for ensuring the execution model is path-independent:
    // the result depends only on the turn's content, not the execution path.
}

/// Conflict detection: two fast-path turns touching the same cell conflict.
#[test]
#[ignore = "TODO: implement conflict detection for concurrent fast-path turns"]
fn test_fast_path_conflict_detection() {
    // TODO: Steps to implement:
    // 1. Alice submits two fast-path turns that both write to the same cell field.
    // 2. The system must detect the conflict and either:
    //    a) Reject the second turn, OR
    //    b) Route both to consensus for ordering.
    // 3. Assert that no double-write occurs.
}
