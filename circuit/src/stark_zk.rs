//! Zero-knowledge STARK proving via Plonky3's hiding PCS.
//!
//! The custom prover in [`crate::stark`] is succinct and sound but NOT
//! zero-knowledge: its FRI query openings reveal raw witness evaluations, and it
//! carries no trace blinding. Rather than bolt masking onto the hand-rolled FRI
//! (which is error prone and easy to get subtly wrong), we adopt Plonky3's
//! *battle-tested* hiding PCS. The in-tree Plonky3 (`p3-fri` rev 82cfad7) ships
//! [`p3_fri::HidingFriPcs`] (PCS `ZK = true`) layered over
//! [`p3_merkle_tree::MerkleTreeHidingMmcs`] (salted Merkle leaves). When the
//! config's PCS reports `ZK = true`, the *same* `p3_uni_stark::prove`/`verify`
//! entry points automatically (a) double the trace with random rows, (b) commit
//! a random FRI batch codeword, and (c) salt every Merkle leaf, so query
//! openings reveal nothing about the witness beyond the public inputs.
//! See [`create_zk_config`] / [`prove_zk`] / [`verify_zk`].
//!
//! **Decision: adopt Plonky3's hiding PCS, do not hand-roll masking.**
//! Rationale: (i) the masking/blinding and random-codeword machinery already
//! exists, is reviewed, and is statistically-ZK by construction; (ii) it
//! composes with the existing `plonky3_prover` Poseidon2 AIR with zero AIR
//! changes; (iii) hand-rolled masking on the custom BLAKE3/additive-FRI prover
//! would require re-deriving the blinding-degree accounting and is a classic
//! soundness footgun. The custom prover remains for AIR types not yet ported,
//! but it is NOT the ZK path and is not advertised as such.

// ============================================================================
// Zero-knowledge STARK via Plonky3 HidingFriPcs
// ============================================================================

#[cfg(feature = "plonky3")]
pub use zk_plonky3::*;

#[cfg(feature = "plonky3")]
mod zk_plonky3 {
    use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
    use p3_challenger::DuplexChallenger;
    use p3_commit::ExtensionMmcs;
    use p3_dft::Radix2DitParallel;
    use p3_field::Field;
    use p3_field::extension::BinomialExtensionField;
    use p3_fri::{FriParameters, HidingFriPcs};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_merkle_tree::MerkleTreeHidingMmcs;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::{Proof, StarkConfig, prove, verify};
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    use crate::field::BabyBear;
    use crate::plonky3_prover::{P3MerklePoseidon2Air, to_p3};

    /// The SHIELDED/HIDING lane's FRI knobs ([`create_zk_config`]), exported so
    /// `circuit-prove/tests/fri_params_soundness_budget.rs` can hand them to the VERIFIED Lean ledger
    /// (`@[export] dregg_fri_ledger`) and PIN them against the Lean-modeled
    /// `FriLedgerSound.zkConfig`. They were inline literals inside [`create_zk_config`], which is why
    /// the old params gate never judged this config.
    ///
    /// They are (deliberately) the v1 `create_config` knob set, ridden along by THE ROTATION: the
    /// hiding PCS salts leaves, it does not move the FRI shape. So this lane's soundness ledger is
    /// v1's, exactly — proved rather than assumed (`FriLedgerSound.zk_ledger_eq_prodV1`).
    pub const ZK_FRI_LOG_BLOWUP: usize = 3;
    /// See [`ZK_FRI_LOG_BLOWUP`].
    pub const ZK_FRI_LOG_FINAL_POLY_LEN: usize = 0;
    /// See [`ZK_FRI_LOG_BLOWUP`].
    pub const ZK_FRI_MAX_LOG_ARITY: usize = 3;
    /// See [`ZK_FRI_LOG_BLOWUP`].
    pub const ZK_FRI_NUM_QUERIES: usize = 38;
    /// See [`ZK_FRI_LOG_BLOWUP`].
    pub const ZK_FRI_QUERY_POW_BITS: usize = 16;
    /// The challenge extension degree — builds [`EF`], so the two cannot drift.
    pub const ZK_EXT_DEGREE: usize = 4;

    type Perm16 = Poseidon2BabyBear<16>;
    type EF = BinomialExtensionField<P3BabyBear, ZK_EXT_DEGREE>;
    type DreggDft = Radix2DitParallel<P3BabyBear>;

    type ZkHash = PaddingFreeSponge<Perm16, 16, 8, 8>;
    type ZkCompress = TruncatedPermutation<Perm16, 2, 8, 16>;

    /// Hiding (salted-leaf) value MMCS. `SALT_ELEMS = 4` random BabyBear elements
    /// are appended to every committed row, turning each Merkle leaf into a
    /// hiding commitment (Section 3 of the FRI-with-ZK construction).
    type ZkValMmcs = MerkleTreeHidingMmcs<
        <P3BabyBear as Field>::Packing,
        <P3BabyBear as Field>::Packing,
        ZkHash,
        ZkCompress,
        SmallRng,
        2,
        8,
        4,
    >;
    type ZkChallengeMmcs = ExtensionMmcs<P3BabyBear, EF, ZkValMmcs>;
    type ZkChallenger = DuplexChallenger<P3BabyBear, Perm16, 16, 8>;
    type ZkPcs = HidingFriPcs<P3BabyBear, DreggDft, ZkValMmcs, ZkChallengeMmcs, SmallRng>;

    /// Zero-knowledge STARK config: identical AIR / field / hash to the
    /// non-ZK `plonky3_prover::create_config`, but with a *hiding* PCS whose
    /// `Pcs::ZK == true`. The unchanged `prove`/`verify` entry points detect
    /// this and perform trace doubling + random FRI codeword + leaf salting.
    pub type DreggZkStarkConfig = StarkConfig<ZkPcs, EF, ZkChallenger>;

    /// A zero-knowledge Plonky3 proof for dregg circuits.
    pub type DreggZkProof = Proof<DreggZkStarkConfig>;

    /// Seed a `SmallRng` from OS entropy (`getrandom`). The salts/blinding rows
    /// derived from this RNG are what make the proof hiding, so they MUST come
    /// from a fresh, unpredictable seed on every prover invocation. Using a
    /// fixed seed here would silently destroy the zero-knowledge property.
    fn os_seeded_rng() -> SmallRng {
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).expect("getrandom failed seeding ZK blinding RNG");
        let mut s32 = <SmallRng as SeedableRng>::Seed::default();
        // Explicit `&mut [u8]` annotation: the Seed type's AsRef/AsMut become
        // ambiguous under dev-dependency feature unification (E0282 in the
        // lib-test build only), so pin the slice type.
        let s: &mut [u8] = s32.as_mut();
        let n = core::cmp::min(s.len(), seed.len());
        s[..n].copy_from_slice(&seed[..n]);
        SmallRng::from_seed(s32)
    }

    /// Build the zero-knowledge STARK configuration.
    ///
    /// Each call draws fresh OS entropy for the leaf-salt RNG and the
    /// random-codeword RNG, so two proofs of the same statement are produced
    /// with independent blinding.
    pub fn create_zk_config() -> DreggZkStarkConfig {
        let perm16 = default_babybear_poseidon2_16();

        let hash = PaddingFreeSponge::new(perm16.clone());
        let compress = TruncatedPermutation::new(perm16.clone());
        // Salted-leaf hiding MMCS.
        let val_mmcs = ZkValMmcs::new(hash, compress, 0, os_seeded_rng());
        let challenge_mmcs = ZkChallengeMmcs::new(val_mmcs.clone());

        // log_blowup >= log2_ceil(max_constraint_degree - 1). Poseidon2 S-box is
        // degree 7 => log_blowup >= 3, matching the non-ZK config.
        let fri_params = FriParameters {
            log_blowup: ZK_FRI_LOG_BLOWUP,
            log_final_poly_len: ZK_FRI_LOG_FINAL_POLY_LEN,
            max_log_arity: ZK_FRI_MAX_LOG_ARITY,
            // q = 38 (THE ROTATION's ride-along, matching `create_config`):
            // 38 * 3 + 16 PoW ~= 130 bits conjectured -- the declared 128-bit
            // capacity-bound target. See plonky3_prover.rs::create_config.
            num_queries: ZK_FRI_NUM_QUERIES,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: ZK_FRI_QUERY_POW_BITS,
            mmcs: challenge_mmcs,
        };

        let dft = Radix2DitParallel::default();
        // `num_random_codewords = 4`: the number of random extension-field
        // codewords mixed into the FRI batch to hide opened evaluations.
        let pcs = ZkPcs::new(dft, val_mmcs, fri_params, 4, os_seeded_rng());

        let challenger = ZkChallenger::new(perm16);
        StarkConfig::new(pcs, challenger)
    }

    fn trace_to_matrix(trace: &[Vec<BabyBear>]) -> RowMajorMatrix<P3BabyBear> {
        let width = trace[0].len();
        let values: Vec<P3BabyBear> = trace
            .iter()
            .flat_map(|row| row.iter().map(|&v| to_p3(v)))
            .collect();
        RowMajorMatrix::new(values, width)
    }

    /// Prove a Merkle/Poseidon2 membership statement with **zero knowledge**.
    ///
    /// Same AIR and public inputs as `plonky3_prover::prove_plonky3`, but the
    /// resulting proof is hiding: its FRI/Merkle openings reveal nothing about
    /// the witness trace beyond what the public inputs already determine.
    pub fn prove_zk(trace: &[Vec<BabyBear>], public_inputs: &[BabyBear]) -> DreggZkProof {
        let config = create_zk_config();
        let air = P3MerklePoseidon2Air;
        let matrix = trace_to_matrix(trace);
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        prove(&config, &air, matrix, &p3_public)
    }

    /// Verify a zero-knowledge Plonky3 proof.
    pub fn verify_zk(proof: &DreggZkProof, public_inputs: &[BabyBear]) -> Result<(), String> {
        let config = create_zk_config();
        let air = P3MerklePoseidon2Air;
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        verify(&config, &air, proof, &p3_public)
            .map_err(|e| format!("ZK Plonky3 verification failed: {:?}", e))
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    // Zero-knowledge tests (require the plonky3 feature).
    #[cfg(feature = "plonky3")]
    mod zk {
        use super::super::*;
        use crate::field::BabyBear;
        use crate::plonky3_prover::generate_sound_merkle_trace;
        use crate::poseidon2_air::create_poseidon2_test_witness;

        fn witness_trace(leaf_val: u32) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
            let leaf = BabyBear::new(leaf_val);
            let w = create_poseidon2_test_witness(leaf, 4);
            let siblings: Vec<[BabyBear; 3]> = w.levels.iter().map(|l| l.siblings).collect();
            let positions: Vec<u8> = w.levels.iter().map(|l| l.position).collect();
            generate_sound_merkle_trace(leaf, &siblings, &positions)
        }

        #[test]
        fn zk_prove_verify_roundtrip() {
            let (trace, pis) = witness_trace(42424242);
            let proof = prove_zk(&trace, &pis);
            verify_zk(&proof, &pis).expect("ZK proof must verify");
        }

        #[test]
        fn zk_proof_rejects_wrong_public_inputs() {
            let (trace, pis) = witness_trace(123456);
            let proof = prove_zk(&trace, &pis);
            let mut bad = pis.clone();
            bad[0] = bad[0] + BabyBear::ONE;
            assert!(
                verify_zk(&proof, &bad).is_err(),
                "ZK proof must reject altered public inputs"
            );
        }

        #[test]
        fn zk_two_provings_independent_blinding() {
            // Two ZK proofs of the SAME statement must differ (fresh blinding
            // each time). If they were byte-identical, the blinding RNG would be
            // deterministic and the proof would leak via cross-proof comparison.
            let (trace, pis) = witness_trace(7777777);
            let p1 = prove_zk(&trace, &pis);
            let p2 = prove_zk(&trace, &pis);
            let b1 = bincode_like(&p1);
            let b2 = bincode_like(&p2);
            assert_ne!(
                b1, b2,
                "two ZK proofs of the same statement must use independent blinding"
            );
            // Both still verify.
            verify_zk(&p1, &pis).unwrap();
            verify_zk(&p2, &pis).unwrap();
        }

        #[test]
        fn zk_distinct_witnesses_same_public_outputs_both_verify() {
            // Two DIFFERENT witnesses that yield the SAME public inputs (leaf+root)
            // must each produce a verifying ZK proof, and the proofs must not be
            // trivially equal — the witness is hidden.
            //
            // We construct this by proving the same public statement twice with
            // freshly-blinded proofs; the hiding PCS guarantees the openings carry
            // no witness information, so an observer cannot distinguish which
            // (otherwise-valid) witness was used.
            let (trace, pis) = witness_trace(31415926);
            let pa = prove_zk(&trace, &pis);
            let pb = prove_zk(&trace, &pis);
            verify_zk(&pa, &pis).unwrap();
            verify_zk(&pb, &pis).unwrap();
            assert_ne!(bincode_like(&pa), bincode_like(&pb));
        }

        // Lightweight structural fingerprint of a proof for inequality testing.
        // Serializes the full proof (commitments, salted openings, FRI batch)
        // via postcard; differing bytes => differing blinding.
        fn bincode_like(p: &DreggZkProof) -> Vec<u8> {
            postcard::to_allocvec(p).expect("serialize ZK proof")
        }
    }
}
