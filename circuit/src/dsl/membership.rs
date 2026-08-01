//! DSL-native Merkle Poseidon2 membership — AIR-name constants and legacy type re-exports.
//!
//! # ⚑ THE ONE-FELT PATH IS DELETED (felt-width finding #9 cutover)
//!
//! This module used to hold `generate_merkle_poseidon2_trace` and
//! `generate_blinded_merkle_poseidon2_trace`: the PRODUCTION root computations. Each chained
//! `hash_4_to_1(children arranged by position)` — a genuine 16-wide Poseidon2 permutation whose
//! result was then **truncated to `state.state[0]`, one BabyBear felt** — level to level, so every
//! interior node and the committed root were ~31-bit commitments. "It is a hash image" does not
//! rescue that: the bottleneck is the OUTPUT WIDTH, and a 31-bit codomain is collided at 2^15.5 —
//! milliseconds — by an attacker who contributes to or mints a subtree, yielding a second
//! authentication path to the SAME authorized root for a key never in the set.
//!
//! Both generators, and the 1-felt `create_test_witness` beside them, are **gone**. The membership
//! family's node is now the full 8-felt `node8` fold in
//! [`crate::membership_descriptor_4ary`] (`node8_4ary`), and the blinded family's is in
//! [`crate::blinded_membership_witness`]. There is deliberately no narrow twin left to drift
//! against — the widened builder is the only membership witness builder in the tree.
//!
//! # What remains here
//!
//! - the AIR-name constants used for descriptor dispatch;
//! - a re-export of the WIDE [`create_test_witness`] so existing call sites keep their import path
//!   (their *types* change from `BabyBear` to `[BabyBear; 8]`, which is the intended hard break);
//! - the legacy `merkle_types` re-exports.

use crate::dsl::descriptors;

// ============================================================================
// Witness generation — the WIDE (8-felt `node8`) builders
// ============================================================================

pub use crate::membership_descriptor_4ary::{
    Digest8, create_test_witness, membership_root_4ary, membership_witness_4ary, node8_4ary,
};

// ============================================================================
// Legacy compatibility types (re-exported from merkle_types.rs)
// ============================================================================

pub use crate::merkle_types::{
    MERKLE_AIR_WIDTH, MerkleAir, MerkleLevelWitness, MerkleWitness, TREE_DEPTH,
    create_test_witness as create_test_witness_legacy,
};

// ============================================================================
// AIR Name Constants (for dispatch)
// ============================================================================

/// The AIR name for standard DSL Merkle Poseidon2 membership proofs.
pub const MERKLE_POSEIDON2_AIR_NAME: &str = descriptors::MERKLE_POSEIDON2_AIR_NAME;

/// The AIR name for blinded DSL Merkle membership proofs.
pub const BLINDED_MERKLE_AIR_NAME: &str = descriptors::BLINDED_MERKLE_AIR_NAME;
