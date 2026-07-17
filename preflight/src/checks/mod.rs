pub mod apps;
pub mod backends;
pub mod blocklace;
pub mod boot;
pub mod bridges;
pub mod caps;
pub mod captp;
pub mod cells;
pub mod cli;
pub mod composition;
// The MIGRATED derivation+membership composite (replaces the stark-killed
// `dregg_circuit::{prove,verify}_authorization_with_membership`): the emitted
// `dregg-derivation-v1` + 4-ary Merkle-membership descriptors, bound together.
pub mod demo_agent;
pub mod derivation_descriptor;
pub mod effect_vm;
pub mod federation;
pub mod intents;
// THE ONE REAL TURN MINTER + shared honest whole-chain fold: every IVC check
// (sovereign, composition, backends, proofs) mints through this module and
// verifies with `ivc_turn_chain::verify_whole_chain_proof_bytes` — the mock
// `dregg_circuit::ivc` simulation is purged from the promotion gate.
pub mod ivc_real;
pub mod lean_marshal;
pub mod nameservice;
pub mod node;
pub mod privacy;
pub mod proofs;
pub mod relay;
pub mod routing;
pub mod solver;
pub mod sovereign;
pub mod storage;
pub mod turns;
pub mod wire;

// Preflight gate for the substrate-correctness mandate: lightweight
// sanity checks that the cell-side StateConstraint evaluator and the
// γ.2 canonical id derivations behave as documented. If these fail,
// none of the heavier substrate tests are worth running.
pub mod state_constraints;

// Preflight: bridge phase-log + portable-note sanity checks. Smoke
// tests for `dregg_cell_crypto::note_bridge` invariants. Separate from
// `bridges.rs` (Mina bridge state machine).
pub mod note_bridge;
