//! Anonymous credential presentation using ring membership proofs.
//!
//! Allows a holder to prove "I am a member of this set" without revealing
//! WHICH member they are. Uses the BlindedMerklePoseidon2StarkAir to generate
//! a ring membership proof over a Merkle tree of credential commitments.

use crate::credential::Credential;
use pyana_circuit::field::BabyBear;
use pyana_circuit::merkle_air::MerkleWitness;
use pyana_circuit::poseidon2;
use pyana_circuit::stark::{self, StarkProof};

/// A registry of credential commitments for anonymous membership proofs.
///
/// Contains the Poseidon2 Merkle tree over all valid credential commitments.
/// A holder proves they have a credential whose commitment is in this tree
/// without revealing which one.
pub struct AnonymousRegistry {
    /// All credential commitments in the registry.
    commitments: Vec<BabyBear>,
    /// Merkle tree depth.
    depth: usize,
    /// Computed root.
    root: BabyBear,
}

impl AnonymousRegistry {
    /// Create a new anonymous registry from credential commitments.
    pub fn new(commitments: Vec<BabyBear>, depth: usize) -> Self {
        let root = Self::compute_root(&commitments, depth);
        Self {
            commitments,
            depth,
            root,
        }
    }

    /// Compute the Merkle root.
    fn compute_root(commitments: &[BabyBear], depth: usize) -> BabyBear {
        let capacity = 4usize.pow(depth as u32);
        let mut level: Vec<BabyBear> = Vec::with_capacity(capacity);
        level.extend_from_slice(commitments);
        level.resize(capacity, BabyBear::ZERO);

        for _ in 0..depth {
            let mut next_level = Vec::with_capacity(level.len() / 4);
            for chunk in level.chunks(4) {
                next_level.push(poseidon2::hash_4_to_1(&[
                    chunk[0], chunk[1], chunk[2], chunk[3],
                ]));
            }
            level = next_level;
        }

        assert_eq!(level.len(), 1);
        level[0]
    }

    /// Get the registry root.
    pub fn root(&self) -> BabyBear {
        self.root
    }

    /// Number of members in the registry.
    pub fn num_members(&self) -> usize {
        self.commitments.len()
    }

    /// Check if a commitment is in the registry.
    pub fn contains(&self, commitment: &BabyBear) -> bool {
        self.commitments.contains(commitment)
    }

    /// Generate a Merkle membership witness for a credential commitment.
    ///
    /// Returns a MerkleWitness suitable for STARK proof generation.
    pub fn membership_witness(&self, commitment: &BabyBear) -> Option<MerkleWitness> {
        use pyana_circuit::merkle_air::MerkleLevelWitness;

        let position = self.commitments.iter().position(|c| c == commitment)?;

        let capacity = 4usize.pow(self.depth as u32);
        let mut padded = Vec::with_capacity(capacity);
        padded.extend_from_slice(&self.commitments);
        padded.resize(capacity, BabyBear::ZERO);

        let mut levels = Vec::with_capacity(self.depth);
        let mut level = padded;
        let mut idx = position;

        for _ in 0..self.depth {
            let group_base = (idx / 4) * 4;
            let pos_in_group = (idx % 4) as u8;

            let mut siblings = [BabyBear::ZERO; 3];
            let mut sib_idx = 0;
            for i in 0..4 {
                if i == pos_in_group as usize {
                    continue;
                }
                siblings[sib_idx] = level[group_base + i];
                sib_idx += 1;
            }
            levels.push(MerkleLevelWitness {
                position: pos_in_group,
                siblings,
            });

            let mut next_level = Vec::with_capacity(level.len() / 4);
            for chunk in level.chunks(4) {
                next_level.push(poseidon2::hash_4_to_1(&[
                    chunk[0], chunk[1], chunk[2], chunk[3],
                ]));
            }
            level = next_level;
            idx = idx / 4;
        }

        Some(MerkleWitness {
            leaf_hash: *commitment,
            levels,
            expected_root: self.root,
        })
    }

    /// Generate an anonymous membership proof for a credential.
    ///
    /// The proof demonstrates that the credential's commitment is in the registry
    /// without revealing which entry it corresponds to. A fresh blinding factor
    /// ensures unlinkability across presentations.
    pub fn prove_anonymous_membership(
        &self,
        credential: &Credential,
        blinding_factor: BabyBear,
    ) -> Option<AnonymousMembershipProof> {
        let witness = self.membership_witness(&credential.commitment)?;

        // Generate the blinded Merkle proof using Poseidon2.
        let action_commitment = pyana_circuit::binding::compute_action_binding(
            "anonymous-membership",
            "credential-registry",
        );

        let proof = pyana_circuit::presentation::generate_blinded_merkle_poseidon2_stark_proof(
            &witness,
            blinding_factor,
            &action_commitment,
            None,
            None,
        )?;

        Some(AnonymousMembershipProof {
            registry_root: self.root,
            blinded_leaf: poseidon2::hash_2_to_1(credential.commitment, blinding_factor),
            stark_proof: proof,
        })
    }
}

/// An anonymous membership proof: proves "I am a member" without revealing which one.
#[derive(Clone, Debug)]
pub struct AnonymousMembershipProof {
    /// The registry root this proof is against.
    pub registry_root: BabyBear,
    /// The blinded leaf (unlinkable across presentations).
    pub blinded_leaf: BabyBear,
    /// The STARK proof.
    pub stark_proof: StarkProof,
}

impl AnonymousMembershipProof {
    /// Verify the anonymous membership proof.
    ///
    /// The verifier checks:
    /// 1. The STARK proof is valid
    /// 2. The registry root matches the expected value
    ///
    /// The verifier does NOT learn which member produced the proof.
    pub fn verify(&self, expected_root: BabyBear) -> bool {
        if self.registry_root != expected_root {
            return false;
        }

        // Verify the STARK proof.
        use pyana_circuit::poseidon2_air::BlindedMerklePoseidon2StarkAir;
        let public_inputs: Vec<BabyBear> = self
            .stark_proof
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect();

        // Check that the root in public inputs matches.
        if public_inputs.len() < 2 {
            return false;
        }
        if public_inputs[1] != expected_root {
            return false;
        }

        stark::verify(
            &BlindedMerklePoseidon2StarkAir,
            &self.stark_proof,
            &public_inputs,
        )
        .is_ok()
    }
}
