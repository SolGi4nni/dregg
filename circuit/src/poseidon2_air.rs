//! Compatibility surface for Poseidon2 proof witnesses.
//!
//! The former structs in this module advertised Rust-authored AIRs. They had no
//! remaining constraint implementation or callers, and are retired. Standalone
//! arity-2 hashing now consumes the descriptor emitted by
//! `Dregg2.Circuit.Emit.Poseidon2HashEmit`; Merkle membership is re-exported from
//! the witness-only DSL helpers and is proved through the emitted IR2 descriptor
//! in [`crate::merkle_air`].

use crate::descriptor_ir2::{EffectVmDescriptor2, chip_absorb_all_lanes, parse_vm_descriptor2};
use crate::field::BabyBear;
use crate::poseidon2::hash_4_to_1;

/// Exact bytes emitted and pinned by `Poseidon2HashEmit.lean`.
pub const POSEIDON2_HASH_DESCRIPTOR_JSON: &str =
    include_str!("../descriptors/by-name/poseidon2-hash-arity2.json");

/// Parse the Lean-authored standalone arity-2 Poseidon2 descriptor.
pub fn poseidon2_hash_descriptor() -> EffectVmDescriptor2 {
    parse_vm_descriptor2(POSEIDON2_HASH_DESCRIPTOR_JSON)
        .expect("Lean-emitted Poseidon2 hash descriptor must parse")
}

/// Build witness rows and public inputs `[a, b, hash_2_to_1(a,b)]` for the
/// emitted descriptor. This is witness construction only; all algebra is in the
/// included Lean artifact.
pub fn poseidon2_hash_witness(a: BabyBear, b: BabyBear) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    // out0 of the arity-2 absorb IS the digest; after the E7 narrowing the descriptor rides the
    // NARROW chip bus, so the 7 exposed permutation lanes are no longer trace columns at all.
    let lanes = chip_absorb_all_lanes(2, &[a, b]);
    let row = vec![a, b, lanes[0]];
    (vec![row.clone(), row], vec![a, b, lanes[0]])
}

/// Compatibility witness shape used by legacy recursion/ZK tests. It contains
/// data only and carries no constraint evaluator.
#[derive(Clone, Debug)]
pub struct MerklePoseidon2LevelWitness {
    pub position: u8,
    pub siblings: [BabyBear; 3],
}

/// Compatibility Merkle witness used by legacy test fixtures.
#[derive(Clone, Debug)]
pub struct MerklePoseidon2Witness {
    pub leaf_hash: BabyBear,
    pub levels: Vec<MerklePoseidon2LevelWitness>,
    pub expected_root: BabyBear,
}

/// Build deterministic Merkle witness data for tests. Proof algebra is supplied
/// by the Lean-emitted membership descriptor, never by this helper.
pub fn create_poseidon2_test_witness(leaf_hash: BabyBear, depth: usize) -> MerklePoseidon2Witness {
    let mut current = leaf_hash;
    let mut levels = Vec::with_capacity(depth);
    for i in 0..depth {
        let position = (i % 4) as u8;
        let siblings = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];
        let mut children = [BabyBear::ZERO; 4];
        children[position as usize] = current;
        let mut sibling = 0;
        for (slot, child) in children.iter_mut().enumerate() {
            if slot != position as usize {
                *child = siblings[sibling];
                sibling += 1;
            }
        }
        current = hash_4_to_1(&children);
        levels.push(MerklePoseidon2LevelWitness { position, siblings });
    }
    MerklePoseidon2Witness {
        leaf_hash,
        levels,
        expected_root: current,
    }
}

// ⚑ The one-felt trace generators `generate_merkle_poseidon2_trace` /
// `generate_blinded_merkle_poseidon2_trace` were re-exported here. They are DELETED: each chained
// a Poseidon2 permutation truncated to `state.state[0]`, so every interior node and the committed
// root were ~31-bit commitments (collided at 2^15.5 — see
// `circuit/tests/membership_forge_tooth.rs`). The membership witness builders now live in
// `crate::membership_descriptor_4ary` (`membership_witness_4ary`, 8-felt `node8` nodes) and
// `crate::blinded_membership_witness`. Nothing is re-exported in their place on purpose: a
// compatibility shim here is exactly how the narrow shape would survive the cutover.
