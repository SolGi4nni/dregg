//! Backward-compatible re-exports for Merkle AIR types, plus the AUDITED
//! Lean-emitted IR2 Merkle-Poseidon2 membership prove/verify path.
//!
//! The production DSL implementation lives in [`crate::dsl::membership`]; the
//! legacy types are in [`crate::merkle_types`].
//!
//! # Why the p3-batch membership path exists (TCB-shrinking)
//!
//! `dsl::membership::prove_membership_dsl` / `verify_membership_dsl` route the
//! 4-ary Merkle membership proof through the **bespoke** `crate::stark` prover,
//! whose hand-rolled FRI has no terminal low-degree test and never low-degree-
//! tests the trace columns. The full-turn proof's MEMBERSHIP sub-proof leg used
//! that unaudited verifier.
//!
//! This module routes the SAME membership statement through the assured IR2
//! interpreter. Its algebra is emitted by
//! `Dregg2.Circuit.Emit.MerkleMembership4aryEmit`; Rust only parses that exact
//! artifact and constructs witness rows. Poseidon2 is enforced by the emitted
//! chip lookup, with position-validity, child arrangement, hash-chain
//! continuity, and `[leaf, root]` boundary binding all Lean-authored.
//!
//! The proof carries a REAL terminal low-degree test (FRI, via the production
//! `create_config`: log_blowup=3, 38 queries, 16 PoW) and an anti-ghost tooth: a forged `root`
//! (or `leaf`) public input
//! is REJECTED by the audited verifier — see the tests.

pub use crate::merkle_types::{
    MERKLE_AIR_WIDTH, MerkleAir, MerkleLevelWitness, MerkleWitness, TREE_DEPTH,
    compute_parent_poseidon2, create_test_witness,
};

pub use membership_p3::*;

mod membership_p3 {
    use crate::descriptor_ir2::{
        DreggStarkConfig, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };
    use crate::field::BabyBear;
    use crate::membership_descriptor_4ary::{
        Digest8, MEMBERSHIP_4ARY_PI_COUNT, membership_descriptor_of_depth_4ary,
        membership_witness_4ary,
    };

    /// A Merkle-Poseidon2 membership proof interpreted from Lean-emitted IR2.
    pub type MembershipP3Proof = Ir2BatchProof<DreggStarkConfig>;

    /// Errors from the audited p3 Merkle-membership path.
    #[derive(Debug, Clone)]
    pub enum MembershipP3Error {
        /// The witness was malformed (depth < 2, or siblings/positions mismatch).
        InvalidWitness(String),
        /// The audited Plonky3 verifier rejected the proof.
        VerificationFailed(String),
    }

    impl core::fmt::Display for MembershipP3Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                MembershipP3Error::InvalidWitness(r) => {
                    write!(f, "invalid membership witness: {r}")
                }
                MembershipP3Error::VerificationFailed(r) => {
                    write!(f, "p3 membership verification failed: {r}")
                }
            }
        }
    }

    impl std::error::Error for MembershipP3Error {}

    /// Build the sixteen public inputs `[leaf0..leaf7, root0..root7]` for a membership
    /// statement (so a caller can bind them into a composed proof). The `root` is the 8-felt
    /// `node8` fold the `(leaf, siblings, positions)` witness recomputes.
    pub fn membership_public_inputs(
        leaf: Digest8,
        siblings: &[[Digest8; 3]],
        positions: &[u8],
    ) -> Result<Vec<BabyBear>, MembershipP3Error> {
        if siblings.len() < 2 {
            return Err(MembershipP3Error::InvalidWitness(
                "need at least depth 2 for STARK".into(),
            ));
        }
        if siblings.len() != positions.len() {
            return Err(MembershipP3Error::InvalidWitness(
                "siblings/positions length mismatch".into(),
            ));
        }
        let (_trace, pis) = membership_witness_4ary(leaf, siblings, positions)
            .map_err(MembershipP3Error::InvalidWitness)?;
        Ok(pis)
    }

    /// Prove 4-ary Merkle-Poseidon2 membership by interpreting the Lean-emitted
    /// IR2 descriptor through the audited Plonky3 backend.
    ///
    /// Proves that `leaf` is a member of the Poseidon2 Merkle tree whose root is
    /// recomputed from `(siblings, positions)`. The returned proof self-verifies
    /// before return (matching the other migrated AIRs), so a returned proof is one
    /// the audited verifier accepts. The public inputs are `[leaf0..leaf7, root0..root7]`.
    pub fn prove_membership_p3(
        leaf: Digest8,
        siblings: &[[Digest8; 3]],
        positions: &[u8],
    ) -> Result<MembershipP3Proof, MembershipP3Error> {
        if siblings.len() < 2 {
            return Err(MembershipP3Error::InvalidWitness(
                "need at least depth 2 for STARK".into(),
            ));
        }
        if siblings.len() != positions.len() {
            return Err(MembershipP3Error::InvalidWitness(
                "siblings/positions length mismatch".into(),
            ));
        }

        let depth = siblings.len();
        let desc = membership_descriptor_of_depth_4ary(depth);
        let (trace, pis) = membership_witness_4ary(leaf, siblings, positions)
            .map_err(MembershipP3Error::InvalidWitness)?;
        prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .map_err(MembershipP3Error::VerificationFailed)
    }

    /// Verify a Merkle-Poseidon2 membership proof on the AUDITED Plonky3 verifier
    /// (`p3-batch-stark`). `public_inputs` must be `[leaf0..leaf7, root0..root7]` (16 felts).
    ///
    /// The verifier reconstructs `CommonData` from the AIR + the proof's degree
    /// bits — it needs no witness (the genuine standalone-verifier path).
    pub fn verify_membership_p3(
        proof: &MembershipP3Proof,
        public_inputs: &[BabyBear],
    ) -> Result<(), MembershipP3Error> {
        if public_inputs.len() != MEMBERSHIP_4ARY_PI_COUNT {
            return Err(MembershipP3Error::VerificationFailed(format!(
                "membership public inputs must be [leaf0..leaf7, root0..root7] \
                 ({MEMBERSHIP_4ARY_PI_COUNT} felts), got {}",
                public_inputs.len()
            )));
        }
        let desc = membership_descriptor_of_depth_4ary(
            proof
                .degree_bits
                .first()
                .copied()
                .and_then(|bits| 1usize.checked_shl(bits as u32))
                .ok_or_else(|| {
                    MembershipP3Error::VerificationFailed(
                        "membership proof has no valid main-trace degree".into(),
                    )
                })?,
        );
        verify_vm_descriptor2(&desc, proof, public_inputs)
            .map_err(MembershipP3Error::VerificationFailed)
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::membership_descriptor_4ary::{
            DIGEST_W, PI_LEAF, PI_ROOT, create_test_witness, membership_root_4ary,
        };

        fn d8(base: u32) -> Digest8 {
            core::array::from_fn(|k| BabyBear::new(base + k as u32))
        }

        /// Honest membership proves + verifies through the AUDITED p3 verifier, and its sixteen
        /// public inputs ROUND-TRIP: they ARE the leaf and the independently recomputed `node8`
        /// fold, lane for lane — not merely "some digest".
        #[test]
        fn membership_p3_proves_and_verifies_honest() {
            let leaf = d8(42424242);
            let (siblings, positions, root) = create_test_witness(leaf, 4);

            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            assert_eq!(
                pis.len(),
                MEMBERSHIP_4ARY_PI_COUNT,
                "16 PIs: leaf(8) then root(8)"
            );
            assert_eq!(&pis[PI_LEAF..PI_LEAF + DIGEST_W], &leaf[..]);
            assert_eq!(
                &pis[PI_ROOT..PI_ROOT + DIGEST_W],
                &membership_root_4ary(leaf, &siblings, &positions)[..],
                "the published root must BE the recomputed node8 fold"
            );
            assert_eq!(&pis[PI_ROOT..PI_ROOT + DIGEST_W], &root[..]);

            let proof = prove_membership_p3(leaf, &siblings, &positions)
                .expect("honest membership must prove+verify through audited p3");
            verify_membership_p3(&proof, &pis).expect("audited p3 verify accepts honest proof");
        }

        /// Depth-8 honest membership also round-trips.
        #[test]
        fn membership_p3_depth_8() {
            let leaf = d8(7777);
            let (siblings, positions, _root) = create_test_witness(leaf, 8);
            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            let proof = prove_membership_p3(leaf, &siblings, &positions).expect("depth-8 proof");
            verify_membership_p3(&proof, &pis).expect("depth-8 verify");
        }

        /// ANTI-GHOST: a forged `root` public input is REJECTED by the audited verifier — in
        /// EVERY lane. The one-felt family pinned lane 0 alone; all eight are pinned now.
        #[test]
        fn membership_p3_rejects_forged_root_in_every_lane() {
            let leaf = d8(42424242);
            let (siblings, positions, _root) = create_test_witness(leaf, 4);
            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            let proof = prove_membership_p3(leaf, &siblings, &positions).expect("honest proof");

            for lane in 0..DIGEST_W {
                let mut forged = pis.clone();
                forged[PI_ROOT + lane] = forged[PI_ROOT + lane] + BabyBear::new(1);
                assert!(
                    verify_membership_p3(&proof, &forged).is_err(),
                    "SOUNDNESS: a root forged in lane {lane} MUST be rejected"
                );
            }
        }

        /// ANTI-GHOST: a forged `leaf` public input is REJECTED in every lane (the row-0
        /// boundaries pin all eight). Includes the lane-0-EQUAL forgery the retired one-felt
        /// family could not distinguish at all.
        #[test]
        fn membership_p3_rejects_forged_leaf_in_every_lane() {
            let leaf = d8(42424242);
            let (siblings, positions, _root) = create_test_witness(leaf, 4);
            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            let proof = prove_membership_p3(leaf, &siblings, &positions).expect("honest proof");

            for lane in 0..DIGEST_W {
                let mut forged = pis.clone();
                forged[PI_LEAF + lane] = forged[PI_LEAF + lane] + BabyBear::new(1);
                if lane != 0 {
                    assert_eq!(
                        forged[PI_LEAF], pis[PI_LEAF],
                        "lane {lane} forgery shares the lane-0 projection the retired family pinned"
                    );
                }
                assert!(
                    verify_membership_p3(&proof, &forged).is_err(),
                    "SOUNDNESS: a leaf forged in lane {lane} MUST be rejected"
                );
            }
        }

        /// ANTI-GHOST (forged WITNESS): a prover with a leaf that is NOT in the tree cannot
        /// produce a proof verifying against the genuine root.
        #[test]
        fn membership_p3_rejects_non_member_leaf() {
            let leaf = d8(42424242);
            let (siblings, positions, root) = create_test_witness(leaf, 4);

            let non_member = d8(13371337);
            assert_ne!(non_member, leaf);
            if let Ok(proof) = prove_membership_p3(non_member, &siblings, &positions) {
                let mut genuine_pis = Vec::with_capacity(MEMBERSHIP_4ARY_PI_COUNT);
                genuine_pis.extend_from_slice(&non_member);
                genuine_pis.extend_from_slice(&root);
                assert!(
                    verify_membership_p3(&proof, &genuine_pis).is_err(),
                    "SOUNDNESS: a non-member leaf must not verify against the genuine root"
                );
            }
        }
    }
} // mod membership_p3
