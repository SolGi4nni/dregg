//! Plonky3-recursion integration: real in-circuit STARK verification.
//!
//! This module uses the `p3-recursion` crate to produce recursive STARK proofs.
//! Given an inner proof (from our AIR), we generate a proof-of-proof: a STARK that
//! attests "the inner proof is valid" — enabling unbounded recursion.
//!
//! ## Architecture
//!
//! The recursion library requires:
//! 1. A `StarkConfig` for generating/verifying inner proofs (must match what the
//!    in-circuit verifier expects)
//! 2. A wrapper implementing `FriRecursionConfig` that adds verifier parameters
//! 3. A `FriRecursionBackendForExt<D>` that knows how to build the verifier circuit
//!
//! Any AIR that implements `p3-air::Air<InteractionSymbolicBuilder<F, EF>>`
//! automatically satisfies the `RecursiveAir` trait via the blanket impl in
//! `p3-recursion`. The generic uni-STARK helpers remain available for callers
//! that already own an assured AIR. Merkle membership uses the multi-table IR2
//! interpreter over the byte-pinned descriptor emitted by
//! `Dregg2.Circuit.Emit.MerkleMembership4aryEmit`, then enters recursion as a
//! `NativeBatchStark` leaf.
//!
//! ## Configuration
//!
//! - Base field: BabyBear (p = 2^31 - 2^27 + 1)
//! - Extension: BinomialExtensionField<BabyBear, 4> (degree-4)
//! - Hash/Compress/Challenger: Poseidon2 width-16 (matching recursion library)
//! - FRI: log_blowup=3 (required for degree-7 AIR), cap_height=0, max_log_arity=1
//!   — the same blowup is reused for lower-degree AIRs; it costs a little prover
//!   work but the resulting recursion config is shared.

pub mod recursive {
    // ⚑ THE CONFIG AND THE VERIFY HALF NOW LIVE IN `dregg-recursion-verify`, AND ARE RE-EXPORTED
    // HERE. Every path that named `plonky3_recursion_impl::recursive::{DreggRecursionConfig,
    // RecursionVk, recursion_vk_fingerprint, verify_recursive_batch_proof*, create_recursion_*}`
    // still resolves — there is ONE of each in the workspace, not a prove-side original and a
    // verify-side copy. The split line is exactly "does a consumer that only VERIFIES a
    // recursion root need this": if yes it moved, if no (backends, `RecursableAir`, the prove
    // entry points below) it stayed.
    pub use dregg_recursion_verify::config::{
        Challenge, Challenger, D, DIGEST_ELEMS, DreggRecursionConfig, INNER_FRI_MAX_LOG_ARITY,
        INNER_FRI_NUM_QUERIES, InnerFri, InnerStarkConfig, MyPcs, RATE, RECURSION_EXT_DEGREE,
        RECURSION_FRI_COMMIT_POW_BITS, RECURSION_FRI_LOG_BLOWUP, RECURSION_FRI_LOG_FINAL_POLY_LEN,
        RECURSION_FRI_MAX_LOG_ARITY, RECURSION_FRI_NUM_QUERIES, RECURSION_FRI_QUERY_POW_BITS,
        RecursionCompatibleProof, WIDTH, create_recursion_config,
        create_recursion_config_for_inner_fri, create_recursion_config_split_fri,
        create_recursion_config_with_fri, ir2_leaf_wrap_split_config,
    };
    pub use dregg_recursion_verify::verify::{
        RecursionVk, decode_recursive_batch_proof, recursion_vk_fingerprint,
        verify_recursive_batch_proof, verify_recursive_batch_proof_with_config,
        verify_recursive_layer, verify_recursive_layer_bytes,
    };

    use p3_air::{Air, BaseAir};
    use p3_baby_bear::BabyBear as P3BabyBear;
    use p3_lookup::symbolic::InteractionSymbolicBuilder;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_recursion::{
        FriRecursionBackend, ProveNextLayerParams, RecursionInput, RecursionOutput,
        build_and_prove_next_layer, ops::Poseidon2Config,
    };
    use p3_uni_stark::{prove, verify};

    use dregg_circuit::descriptor_ir2::{
        Ir2Air, MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
        prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
    };
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::membership_descriptor_4ary::{
        Digest8, membership_descriptor_of_depth_4ary, membership_witness_4ary,
    };
    use dregg_circuit::plonky3_prover::to_p3;

    /// Create the FRI recursion backend for degree-4 extension.
    ///
    /// The backend holds only a fixed Poseidon2 challenger config (no per-proof state), so it is
    /// built ONCE per thread and cloned on each call (a cheap copy of the config) rather than
    /// re-constructing the permutation tables per leaf. `thread_local` sidesteps any `Sync`
    /// requirement; the cached value is identical to a fresh construction (same deterministic
    /// `BABY_BEAR_D4_W16` config).
    pub fn create_recursion_backend()
    -> p3_recursion::FriRecursionBackendForExt<D, WIDTH, RATE, Poseidon2Config> {
        thread_local! {
            static BACKEND: p3_recursion::FriRecursionBackendForExt<D, WIDTH, RATE, Poseidon2Config> =
                const { FriRecursionBackend::new(Poseidon2Config::BABY_BEAR_D4_W16).for_extension_degree::<D>() };
        }
        BACKEND.with(|b| b.clone())
    }

    /// Create the FRI recursion backend with the `recompose/coeff` table FORCED on.
    ///
    /// Identical to [`create_recursion_backend`] except it sets `with_coeff_lookups()`
    /// (the fork's `force_coeff_lookups` flag), which ORs into the three `cl`
    /// (coeff-lookups) gates in `recursion/src/backend/fri.rs`. For the D=4 width-16
    /// challenger this config uses, `challenger.extension_degree() == D == 4`, so the
    /// default `cl = (challenger_D != D)` is FALSE and the backend would NOT register
    /// the `recompose/coeff` table's prover / preprocessor / air-builder. The flag
    /// overrides that, opting the table in so a `decompose_ext_to_base_coeffs` whose
    /// per-coefficient base values must ride the `WitnessChecks` bus (the custom
    /// PI-commitment expose — 4 CONSECUTIVE base lanes of one ext limb) balances.
    ///
    /// SEPARATE from [`create_recursion_backend`] (left untouched) so existing leaves'
    /// VKs do not move: this backend is used ONLY by the commitment-exposing custom
    /// leaf ([`crate::custom_leaf_adapter::prove_custom_leaf_with_commitment`]). The
    /// table is inert for any leaf that never calls the coeff-ctl decompose path.
    pub fn create_recursion_backend_with_coeff_lookups()
    -> p3_recursion::FriRecursionBackendForExt<D, WIDTH, RATE, Poseidon2Config> {
        thread_local! {
            static BACKEND: p3_recursion::FriRecursionBackendForExt<D, WIDTH, RATE, Poseidon2Config> = const {
                FriRecursionBackend::new(Poseidon2Config::BABY_BEAR_D4_W16)
                    .with_coeff_lookups()
                    .for_extension_degree::<D>()
            };
        }
        BACKEND.with(|b| b.clone())
    }

    /// Trait alias capturing the bounds an AIR must satisfy to flow through this
    /// recursion path. Any AIR implementing `p3-air::Air` against both the
    /// uni-stark prover/verifier and the `InteractionSymbolicBuilder` (which is
    /// what `p3-recursion`'s blanket `RecursiveAir` impl needs) satisfies this.
    ///
    /// Concretely, this means:
    /// 1. `BaseAir<F>` — width + public-value count for the prover/verifier.
    /// 2. `Air<SymbolicAirBuilder<F>>` — what `p3_uni_stark` calls into when
    ///    extracting symbolic constraints prior to proving.
    /// 3. `Air<ProverConstraintFolder<SC>>` and
    ///    `Air<VerifierConstraintFolder<SC>>` — what `p3_uni_stark::prove` and
    ///    `verify` invoke for the standalone inner proof.
    /// 4. `Air<DebugConstraintBuilder<F>>` — what `p3_uni_stark` uses for the
    ///    debug-mode trace consistency check.
    /// 5. `Air<InteractionSymbolicBuilder<F, EF>>` — what the recursion
    ///    library's blanket `RecursiveAir` impl extracts symbolic constraints
    ///    from for the verifier circuit.
    ///
    /// Plus `Sync + 'static` so the proof generator can hand the AIR around.
    pub trait RecursableAir:
        BaseAir<P3BabyBear>
        + for<'a> Air<p3_uni_stark::ProverConstraintFolder<'a, DreggRecursionConfig>>
        + for<'a> Air<p3_uni_stark::VerifierConstraintFolder<'a, DreggRecursionConfig>>
        + for<'a> Air<p3_air::DebugConstraintBuilder<'a, P3BabyBear>>
        + Air<p3_uni_stark::SymbolicAirBuilder<P3BabyBear>>
        + Air<InteractionSymbolicBuilder<P3BabyBear, Challenge>>
        + Sync
        + 'static
    {
    }

    impl<A> RecursableAir for A where
        A: BaseAir<P3BabyBear>
            + for<'a> Air<p3_uni_stark::ProverConstraintFolder<'a, DreggRecursionConfig>>
            + for<'a> Air<p3_uni_stark::VerifierConstraintFolder<'a, DreggRecursionConfig>>
            + for<'a> Air<p3_air::DebugConstraintBuilder<'a, P3BabyBear>>
            + Air<p3_uni_stark::SymbolicAirBuilder<P3BabyBear>>
            + Air<InteractionSymbolicBuilder<P3BabyBear, Challenge>>
            + Sync
            + 'static
    {
    }

    /// Generic inner proof generator: any AIR satisfying [`RecursableAir`]
    /// can be proven with the recursion-compatible STARK config.
    pub fn prove_inner_for_air<A>(
        air: &A,
        trace: RowMajorMatrix<P3BabyBear>,
        public_inputs: &[BabyBear],
    ) -> RecursionCompatibleProof
    where
        A: RecursableAir,
    {
        prove_inner_for_air_with_config(air, trace, public_inputs, &create_recursion_config())
    }

    /// [`prove_inner_for_air`] under an EXPLICIT recursion config — needed when the inner
    /// uni-STARK proof will be wrapped/aggregated at a NON-default FRI engine (e.g. the rotated
    /// fold's [`crate::ivc_turn_chain::ir2_leaf_wrap_config`], log_blowup 6). Building the inner
    /// proof under the same config as the wrap layer keeps the FRI Merkle path lengths consistent
    /// — proving it at the default `create_recursion_config` (log_blowup 3) and then wrapping at
    /// the log_blowup-6 wrap config raises `InvalidProofShape("Fewer siblings in proof than op_ids
    /// provided")` in-circuit.
    pub fn prove_inner_for_air_with_config<A>(
        air: &A,
        trace: RowMajorMatrix<P3BabyBear>,
        public_inputs: &[BabyBear],
        config: &DreggRecursionConfig,
    ) -> RecursionCompatibleProof
    where
        A: RecursableAir,
    {
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        prove(config, air, trace, &p3_public)
    }

    /// Generic inner proof verifier (paired with [`prove_inner_for_air`]).
    pub fn verify_inner_for_air<A>(
        air: &A,
        proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<(), String>
    where
        A: RecursableAir,
    {
        verify_inner_for_air_with_config(air, proof, public_inputs, &create_recursion_config())
    }

    /// [`verify_inner_for_air`] under an EXPLICIT recursion config (paired with
    /// [`prove_inner_for_air_with_config`]).
    pub fn verify_inner_for_air_with_config<A>(
        air: &A,
        proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
        config: &DreggRecursionConfig,
    ) -> Result<(), String>
    where
        A: RecursableAir,
    {
        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();
        verify(config, air, proof, &p3_public)
            .map_err(|e| format!("Recursion-compatible verification failed: {:?}", e))
    }

    /// Produce a recursive proof for any `RecursableAir` inner proof.
    ///
    /// This is the generalized core recursion entry point for an assured
    /// uni-STARK AIR. Descriptor-interpreted statements use the native-batch
    /// entry point, as [`prove_recursive_membership`] does below.
    pub fn prove_recursive_layer_for_air<A>(
        air: &A,
        inner_proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<RecursionOutput<DreggRecursionConfig>, String>
    where
        A: RecursableAir,
    {
        let config = create_recursion_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        let p3_public: Vec<P3BabyBear> = public_inputs.iter().map(|&v| to_p3(v)).collect();

        let input = RecursionInput::UniStark {
            proof: inner_proof,
            air,
            public_inputs: p3_public,
            preprocessed_commit: None,
        };

        build_and_prove_next_layer::<DreggRecursionConfig, A, _, D>(
            &input, &config, &backend, &params,
        )
        .map_err(|e| format!("Recursive proof generation failed: {:?}", e))
    }

    /// End-to-end: interpret the Lean-emitted Merkle-membership descriptor,
    /// prove its IR2 batch, then verify that batch inside one recursion layer.
    ///
    /// The same emitted JSON and witness builder feed the deployed
    /// `dregg_circuit::merkle_air::prove_membership_p3` path. The only
    /// difference here is that the inner batch is minted under the recursion
    /// config type so `RecursionInput::NativeBatchStark` can consume it.
    ///
    /// Leaf and siblings are full 8-felt [`Digest8`] nodes (the `node8` cutover): the folded
    /// statement is the 16-PI `[leaf0..8, root0..8]` one, not the retired 1-felt `[leaf, root]`.
    pub fn prove_recursive_membership(
        leaf_hash: Digest8,
        siblings: &[[Digest8; 3]],
        positions: &[u8],
    ) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
        let desc = membership_descriptor_of_depth_4ary(siblings.len());
        let (trace, public_inputs) = membership_witness_4ary(leaf_hash, siblings, positions)?;
        let config = create_recursion_config();
        let inner_proof = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
            &desc,
            &trace,
            &public_inputs,
            &MemBoundaryWitness::default(),
            &[],
            &UMemBoundaryWitness::default(),
            &config,
        )?;
        verify_vm_descriptor2_with_config(&desc, &inner_proof, &public_inputs, &config)?;

        let (airs, table_public_inputs, common) =
            ir2_airs_and_common_for_config(&desc, &inner_proof, &public_inputs, &config)?;
        let input: RecursionInput<'_, DreggRecursionConfig, Ir2Air> =
            RecursionInput::NativeBatchStark {
                airs: &airs,
                proof: &inner_proof,
                common_data: &common,
                table_public_inputs,
            };
        build_and_prove_next_layer::<DreggRecursionConfig, Ir2Air, _, D>(
            &input,
            &config,
            &create_recursion_backend(),
            &ProveNextLayerParams::default(),
        )
        .map_err(|e| format!("Recursive emitted-membership proof generation failed: {e:?}"))
    }

    // ========================================================================
    // Tests
    // ========================================================================

    #[cfg(test)]
    mod tests {
        use super::*;
        use dregg_circuit::membership_descriptor_4ary::create_test_witness;

        /// Recursion-shape smoke: one layer verifies the assured emitted
        /// membership descriptor's real multi-table IR2 proof in-circuit.
        #[test]
        fn recursive_merkle_poc() {
            let leaf: Digest8 = core::array::from_fn(|k| BabyBear::new(42424242 + k as u32));
            let (siblings, positions, _root) = create_test_witness(leaf, 4);

            let result = prove_recursive_membership(leaf, &siblings, &positions);
            assert!(
                result.is_ok(),
                "Recursive proof generation failed: {:?}",
                result.err()
            );

            let output = result.unwrap();
            let verify_result = verify_recursive_layer(&output);
            assert!(
                verify_result.is_ok(),
                "Recursive proof verification failed: {:?}",
                verify_result.err()
            );
        }
    }
}
