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
//! See [`create_zk_config`]; concrete hiding prove/verify entry points live beside
//! the AIRs they instantiate (for example `dsl_p3_air::prove_dsl_zk` and
//! `cert_f_air::prove_cert_f_zk`).
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
    use p3_merkle_tree::MerkleTreeHidingMmcs;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::{Proof, StarkConfig};
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

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
    /// **The SIXTH knob** — plonky3's `commit_proof_of_work_bits`, ground per fold round against
    /// exactly the phase BCIKS20's `ε_C` bounds. It was an inline `0` in the `FriParameters` below;
    /// exported for the same reason as the five above, so the params gate can pin the value the
    /// prover grinds. Capped at 30 by `grind`'s single-BabyBear-witness assertion.
    pub const ZK_FRI_COMMIT_POW_BITS: usize = 0;
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
            // q = 38 (THE ROTATION's ride-along, matching `create_config`).
            // The old `38 * 3 + 16 ~= 130` capacity-radius estimate is only a
            // conjectural comparison column, not an accepted 128-bit soundness
            // budget; deployment claims use the proven/Johnson ledger. See
            // `docs/reference/FRI-BOTH-WIN-LEVERS.md` and the matching non-ZK
            // configuration in `plonky3_prover.rs`.
            num_queries: ZK_FRI_NUM_QUERIES,
            commit_proof_of_work_bits: ZK_FRI_COMMIT_POW_BITS,
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
}
