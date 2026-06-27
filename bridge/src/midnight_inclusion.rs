//! Native state-INCLUSION proofs for the Midnight bridge.
//!
//! See `docs/deos/DIFFERENT-MIDNIGHT-BRIDGE.md` for the full design. The short
//! version:
//!
//! Midnight cannot verify dregg's FRI transition proof (Halo2+KZG/BLS12-381, no
//! STARK backend, no recursion in Compact — `docs/deos/ZKIR-V3.md`). But the
//! question a relying Midnight contract actually needs answered — *"does cell X
//! hold committed state Y?"* — is a **Merkle inclusion**, which Compact's
//! standard library checks natively via `merkleTreePathRoot` (Poseidon over the
//! BLS12-381 scalar field).
//!
//! ## The field/hash mismatch (why this is a *mirror*, not dregg's own root)
//!
//! dregg's state roots ([`cell::state::compute_fields_root`] / `compute_heap_root`)
//! are sorted **Poseidon2 over BabyBear** (31-bit) Merkle roots. Compact's
//! Merkle gadget is **Poseidon over BLS12-381 `Fq`** (255-bit). These are
//! different hashes over different fields, so Compact *cannot* recompute dregg's
//! native root without emulating BabyBear-Poseidon2 in BLS constraints (the
//! FRI-class cost, no tooling). Verifying dregg's own root natively is infeasible.
//!
//! The feasible shape is a **re-commitment**: a relay re-hashes the dregg cell-
//! state commitments under *Midnight's* Poseidon-over-BLS into a mirror tree, and
//! the mirror root `R_mid` is what Midnight checkpoints (optimistically, bonded,
//! watchtower-backed). Inclusion against `R_mid` is then fully native in Compact.
//!
//! This module is the **dregg-side** half: the mirror-tree builder + the
//! inclusion-proof message type whose shape mirrors the Compact
//! `MerkleTreePath<DEPTH, Field>` ADT.
//!
//! ## Load-bearing TODO
//!
//! [`mirror_leaf`] / [`mirror_node`] currently use a BLAKE3-based placeholder so
//! the tree is *structurally* correct and the message type / verification logic
//! are exercised. To be **hash-compatible with Compact** (so a path this builder
//! emits actually re-roots to `R_mid` under `merkleTreePathRoot` on Midnight),
//! these must compute the **same BLS-field Poseidon** Midnight uses — see
//! `~/midnight/midnight-ledger/transient-crypto/src/hash.rs::transient_hash`
//! (the canonical implementation) or `~/midnight/midnight-zk` Poseidon
//! (width-3, rate-2, 8 full + 60 partial rounds over `midnight_curves::Fq`).
//! Wiring that real hash is the first concrete task. See `TODO(mirror-hash)`.

use serde::{Deserialize, Serialize};

/// A Midnight field element, in wire form. On Midnight this is a BLS12-381
/// scalar (`Fq`, 255-bit); here it is its canonical 32-byte little-endian
/// encoding. Compact would see this as a `Field` / `MerkleTreeDigest.field`.
pub type Field = [u8; 32];

/// Domain-separation tag for the placeholder mirror leaf hash.
///
/// TODO(mirror-hash): the real leaf is `transientHash([cell_id, state])` under
/// Midnight's Poseidon; this BLAKE3 stand-in is structurally faithful only.
const MIRROR_LEAF_TAG: &str = "dregg-midnight-mirror-leaf-v1";
/// Domain-separation tag for the placeholder mirror inner-node hash.
const MIRROR_NODE_TAG: &str = "dregg-midnight-mirror-node-v1";

/// Hash a dregg cell-state commitment into a mirror **leaf** `Field`.
///
/// On Midnight the corresponding leaf is `transientHash([cell_id_field,
/// state_commitment_field])`; a Compact contract that hashes its disclosed
/// `(cell_id, state)` the same way will reproduce this leaf.
///
/// TODO(mirror-hash): replace the BLAKE3 body with BLS-field Poseidon.
pub fn mirror_leaf(cell_id: &[u8; 32], state_commitment: &[u8; 32]) -> Field {
    let mut h = blake3::Hasher::new_derive_key(MIRROR_LEAF_TAG);
    h.update(cell_id);
    h.update(state_commitment);
    *h.finalize().as_bytes()
}

/// Hash two child `Field`s into a parent `Field` (the inner Merkle node).
///
/// TODO(mirror-hash): replace with BLS-field Poseidon-2 compression to match
/// Compact's `merkleTreePathRoot` node hash.
pub fn mirror_node(left: &Field, right: &Field) -> Field {
    let mut h = blake3::Hasher::new_derive_key(MIRROR_NODE_TAG);
    h.update(left);
    h.update(right);
    *h.finalize().as_bytes()
}

/// One step of a mirror inclusion path: a sibling digest plus which side it is
/// on. Mirrors Compact's `MerkleTreePathEntry` (sibling + left/right).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MirrorPathEntry {
    /// The sibling node's digest.
    pub sibling: Field,
    /// `true` if the sibling is the **right** child (i.e. our node is the left
    /// child) at this level; `false` if the sibling is the left child.
    pub sibling_is_right: bool,
}

/// A native-inclusion proof: "`cell_id` holds `state_commitment`, committed
/// under the checkpointed mirror root."
///
/// This is the message a prover submits; a Compact contract reconstructs the
/// root from `(cell_id, state_commitment) → leaf` + `path` and compares it to
/// the sealed checkpoint (`dregg_inclusion.compact::verifyInclusion`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MirrorInclusionProof {
    /// The cell whose state is being proven included.
    pub cell_id: [u8; 32],
    /// The cell's committed state (e.g. its canonical state commitment / a
    /// `fields_root`), re-hashed into the mirror leaf.
    pub state_commitment: [u8; 32],
    /// Path from the leaf up to the root, leaf-adjacent entry first.
    pub path: Vec<MirrorPathEntry>,
}

impl MirrorInclusionProof {
    /// Recompute the mirror root this proof attests to, by folding the path.
    ///
    /// This is the exact computation `merkleTreePathRoot(path)` performs on
    /// Midnight (modulo the TODO(mirror-hash) hash swap).
    pub fn recompute_root(&self) -> Field {
        let mut acc = mirror_leaf(&self.cell_id, &self.state_commitment);
        for step in &self.path {
            acc = if step.sibling_is_right {
                mirror_node(&acc, &step.sibling)
            } else {
                mirror_node(&step.sibling, &acc)
            };
        }
        acc
    }

    /// Verify the proof against a checkpointed mirror root.
    ///
    /// Returns `true` iff folding the path reproduces `checkpoint_root`. This is
    /// the dregg-side mirror of the native Compact check
    /// `merkleTreePathRoot(path) == mirrorRoot`.
    pub fn verify(&self, checkpoint_root: &Field) -> bool {
        &self.recompute_root() == checkpoint_root
    }
}

/// A mirror Merkle tree over dregg cell-state commitments, built with Midnight's
/// (placeholder) hash. The relay maintains one of these in lockstep with dregg's
/// native Poseidon2/BabyBear state; its [`root`](MirrorTree::root) is the
/// `R_mid` posted to Midnight as an optimistic checkpoint.
///
/// A simple fixed-arity binary tree padded to a power of two with a zero
/// sentinel leaf, so depth is uniform and paths are a fixed length.
#[derive(Clone, Debug)]
pub struct MirrorTree {
    /// Leaf digests, in committed (sorted-by-`cell_id`) order.
    leaves: Vec<Field>,
    /// `cell_id` for each leaf index, parallel to `leaves`.
    cell_ids: Vec<[u8; 32]>,
    /// Original `(cell_id, state_commitment)` for path emission.
    states: Vec<[u8; 32]>,
    /// Levels bottom-up: `levels[0]` == padded leaves, last == `[root]`.
    levels: Vec<Vec<Field>>,
}

impl MirrorTree {
    /// The padding sentinel for empty leaf slots.
    const SENTINEL: Field = [0u8; 32];

    /// Build a mirror tree from `(cell_id, state_commitment)` entries.
    ///
    /// Entries are sorted by `cell_id` (order-canonical, like dregg's sorted
    /// roots) and padded with [`Self::SENTINEL`] to the next power of two.
    pub fn build(mut entries: Vec<([u8; 32], [u8; 32])>) -> Self {
        entries.sort_by_key(|a| a.0);
        let cell_ids: Vec<[u8; 32]> = entries.iter().map(|(c, _)| *c).collect();
        let states: Vec<[u8; 32]> = entries.iter().map(|(_, s)| *s).collect();
        let mut leaves: Vec<Field> = entries.iter().map(|(c, s)| mirror_leaf(c, s)).collect();

        let target = leaves.len().max(1).next_power_of_two();
        leaves.resize(target, Self::SENTINEL);

        let mut levels = vec![leaves.clone()];
        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let next: Vec<Field> = cur
                .chunks(2)
                .map(|pair| mirror_node(&pair[0], &pair[1]))
                .collect();
            levels.push(next);
        }

        Self {
            leaves,
            cell_ids,
            states,
            levels,
        }
    }

    /// The mirror root `R_mid` to checkpoint on Midnight.
    pub fn root(&self) -> Field {
        *self.levels.last().unwrap().first().unwrap()
    }

    /// Tree depth (path length) — `log2` of the padded leaf count.
    pub fn depth(&self) -> usize {
        self.levels.len() - 1
    }

    /// Produce an inclusion proof for `cell_id`, if present.
    pub fn prove(&self, cell_id: &[u8; 32]) -> Option<MirrorInclusionProof> {
        let idx = self.cell_ids.iter().position(|c| c == cell_id)?;
        let state_commitment = self.states[idx];

        let mut path = Vec::with_capacity(self.depth());
        let mut node = idx;
        for level in &self.levels[..self.levels.len() - 1] {
            let sibling_is_right = node % 2 == 0; // our node is the left child
            let sibling = level[node ^ 1];
            path.push(MirrorPathEntry {
                sibling,
                sibling_is_right,
            });
            node /= 2;
        }

        Some(MirrorInclusionProof {
            cell_id: *cell_id,
            state_commitment,
            path,
        })
    }

    /// The padded leaf digests (for inspection / fraud-proof openings).
    pub fn leaves(&self) -> &[Field] {
        &self.leaves
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> [u8; 32] {
        [b; 32]
    }

    fn entries(n: u8) -> Vec<([u8; 32], [u8; 32])> {
        (0..n).map(|i| (cid(i), cid(i.wrapping_add(100)))).collect()
    }

    #[test]
    fn single_leaf_round_trips() {
        let tree = MirrorTree::build(entries(1));
        let proof = tree.prove(&cid(0)).unwrap();
        assert!(proof.verify(&tree.root()));
        assert_eq!(proof.recompute_root(), tree.root());
    }

    #[test]
    fn every_member_proves_inclusion() {
        let tree = MirrorTree::build(entries(5)); // pads 5 -> 8 leaves, depth 3
        assert_eq!(tree.depth(), 3);
        for i in 0..5u8 {
            let proof = tree.prove(&cid(i)).unwrap();
            assert!(proof.verify(&tree.root()), "member {i} must verify");
        }
    }

    #[test]
    fn non_member_has_no_proof() {
        let tree = MirrorTree::build(entries(3));
        assert!(tree.prove(&cid(200)).is_none());
    }

    #[test]
    fn wrong_root_rejected() {
        let tree = MirrorTree::build(entries(4));
        let proof = tree.prove(&cid(2)).unwrap();
        let mut bad = tree.root();
        bad[0] ^= 0xFF;
        assert!(!proof.verify(&bad));
    }

    #[test]
    fn tampered_state_breaks_inclusion() {
        let tree = MirrorTree::build(entries(4));
        let mut proof = tree.prove(&cid(2)).unwrap();
        proof.state_commitment[0] ^= 0xFF;
        assert!(
            !proof.verify(&tree.root()),
            "a state that isn't the committed one must not re-root"
        );
    }

    #[test]
    fn tampered_path_breaks_inclusion() {
        let tree = MirrorTree::build(entries(4));
        let mut proof = tree.prove(&cid(1)).unwrap();
        proof.path[0].sibling[0] ^= 0xFF;
        assert!(!proof.verify(&tree.root()));
    }

    #[test]
    fn message_serialization_round_trips() {
        let tree = MirrorTree::build(entries(4));
        let proof = tree.prove(&cid(3)).unwrap();
        let bytes = postcard::to_stdvec(&proof).unwrap();
        let decoded: MirrorInclusionProof = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(decoded, proof);
        assert!(decoded.verify(&tree.root()));
    }
}
