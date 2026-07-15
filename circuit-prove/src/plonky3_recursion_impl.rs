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
//! `p3-recursion`. `P3MerklePoseidon2Air` (358 columns, degree-7) was the first
//! AIR proven through this path; `prove_recursive_layer` is now generic so any
//! `Air`-implementing AIR (e.g., `AggregationAir`, the Effect VM AIR via its
//! `p3-air` bridge) can be wrapped without code duplication.
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
    use std::sync::Arc;

    use p3_air::{Air, BaseAir};
    use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
    use p3_challenger::DuplexChallenger;
    use p3_circuit::{CircuitBuilder, CircuitRunner, NonPrimitiveOpId};
    use p3_circuit_prover::BatchStarkProver;
    use p3_commit::{ExtensionMmcs, Pcs};
    use p3_dft::Radix2DitParallel;
    use p3_field::Field;
    use p3_field::extension::BinomialExtensionField;
    use p3_fri::{FriParameters, TwoAdicFriPcs};
    use p3_lookup::logup::LogUpGadget;
    use p3_lookup::symbolic::InteractionSymbolicBuilder;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_merkle_tree::MerkleTreeMmcs;
    use p3_recursion::pcs::{
        InputProofTargets, MerkleCapTargets, RecValMmcs, set_fri_mmcs_private_data,
    };
    use p3_recursion::traits::RecursiveAir;
    use p3_recursion::{
        FriRecursionBackend, FriRecursionConfig, FriVerifierParams, ProveNextLayerParams,
        RecursionInput, RecursionOutput, build_and_prove_next_layer, ops::Poseidon2Config,
    };
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use p3_uni_stark::{Proof, StarkConfig, StarkGenericConfig, Val, prove, verify};

    use dregg_circuit::field::BabyBear;
    use dregg_circuit::plonky3_prover::{
        P3MerklePoseidon2Air, generate_sound_merkle_trace, to_p3, trace_to_matrix,
    };

    // ========================================================================
    // Type definitions matching the recursion library's expected configuration
    // ========================================================================

    const D: usize = RECURSION_EXT_DEGREE;
    const WIDTH: usize = 16;
    const RATE: usize = 8;
    const DIGEST_ELEMS: usize = 8;

    // ========================================================================
    // The SHIPPED FRI knob sets of this module, exported so
    // `circuit-prove/tests/fri_params_soundness_budget.rs` can hand each one to the VERIFIED Lean
    // ledger (`@[export] dregg_fri_ledger` over `Dregg2.Circuit.FriLedger.friLedger`) and PIN it
    // against its Lean model. They were inline literals inside the two config builders below, which
    // is why the old params gate — which judged only `PROD_FRI_*` and `IR2_FRI_*` — could not see
    // them at all: 5 of the 7 shipped configs were ungated.
    // ========================================================================

    /// The challenge extension degree — `|F| = babyBearP ^ 4 ≈ 2^123.6`, the denominator of every
    /// per-fold proximity-gap bound. Builds [`D`], so the two cannot drift.
    pub const RECURSION_EXT_DEGREE: usize = 4;

    /// [`create_recursion_config`]'s FRI log blowup. Must be `≥ 3`: the AIR has degree-7 constraints
    /// (the `x^7` S-box), so the quotient domain needs blowup `≥ d − 1 = 6`.
    pub const RECURSION_FRI_LOG_BLOWUP: usize = 3;
    /// [`create_recursion_config`]'s FRI query count.
    pub const RECURSION_FRI_NUM_QUERIES: usize = 38;
    /// [`create_recursion_config`]'s FRI query proof-of-work bits — **14, not the 16 every other
    /// shipped config carries**. ⚑ That two-bit difference puts its capacity ledger at exactly
    /// `3·38 + 14 = 128` — on the nose of the drift margin, with zero headroom
    /// (`FriLedgerSound.recursion_ledger_capacityBits`).
    pub const RECURSION_FRI_QUERY_POW_BITS: usize = 14;
    /// [`create_recursion_config`]'s FRI fold arity exponent — 1, i.e. fold by 2.
    pub const RECURSION_FRI_MAX_LOG_ARITY: usize = 1;
    /// [`create_recursion_config`]'s FRI final-polynomial length exponent — 0 (constant final poly).
    pub const RECURSION_FRI_LOG_FINAL_POLY_LEN: usize = 0;

    /// The fold arity exponent [`create_recursion_config_for_inner_fri`] pins — **1 (fold by 2)**,
    /// the knob that makes `ivc_turn_chain::ir2_leaf_wrap_config()` an ARITY-2 config even though
    /// `ir2_config` (which it otherwise matches) is arity 8. See the PROBE note at the call site.
    ///
    /// ⚑ NAME COLLISION worth knowing: the Lean `FriVerifier.ir2LeafWrapConfig` (`maxLogArity = 3`)
    /// models `dregg_circuit::descriptor_ir2::ir2_config`, NOT the Rust fn named
    /// `ir2_leaf_wrap_config()`. The latter's real knob set is `FriLedgerSound.ir2LeafWrapRotatedConfig`
    /// — and being arity-2 at `logBlowup = 6`, it is the ONE shipped config the standing ~112.6-bit
    /// per-fold posture actually describes.
    pub const INNER_FRI_MAX_LOG_ARITY: usize = 1;
    /// The query count [`create_recursion_config_for_inner_fri`] pins — 19, matching `ir2_config`'s
    /// security target at log_blowup 6.
    pub const INNER_FRI_NUM_QUERIES: usize = 19;

    type F = P3BabyBear;
    type Challenge = BinomialExtensionField<F, D>;
    type Dft = Radix2DitParallel<F>;
    type Perm = Poseidon2BabyBear<WIDTH>;
    type MyHash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_ELEMS>;
    type MyCompress = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, WIDTH>;
    type MyMmcs = MerkleTreeMmcs<
        <F as Field>::Packing,
        <F as Field>::Packing,
        MyHash,
        MyCompress,
        2,
        DIGEST_ELEMS,
    >;
    type ChallengeMmcs = ExtensionMmcs<F, Challenge, MyMmcs>;
    type Challenger = DuplexChallenger<F, Perm, WIDTH, RATE>;
    type MyPcs = TwoAdicFriPcs<F, Dft, MyMmcs, ChallengeMmcs>;

    /// The raw STARK config type (without FRI verifier params wrapper).
    type InnerStarkConfig = StarkConfig<MyPcs, Challenge, Challenger>;

    /// The proof type produced by the recursion-compatible prover.
    /// Uses `DreggRecursionConfig` as the SC parameter so it's directly
    /// usable with `RecursionInput` without type mismatches.
    pub type RecursionCompatibleProof = Proof<DreggRecursionConfig>;

    /// FRI proof targets for the in-circuit verifier.
    type InnerFri = p3_recursion::pcs::FriProofTargets<
        F,
        Challenge,
        p3_recursion::pcs::RecExtensionValMmcs<
            F,
            Challenge,
            DIGEST_ELEMS,
            RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>,
        >,
        InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
        p3_recursion::pcs::Witness<F>,
    >;

    // ========================================================================
    // Config wrapper implementing FriRecursionConfig
    // ========================================================================

    /// Wrapper around our STARK config that adds FRI verifier params.
    ///
    /// This implements both `StarkGenericConfig` (by delegation) and
    /// `FriRecursionConfig` (required by the recursion backend).
    #[derive(Clone)]
    pub struct DreggRecursionConfig {
        config: Arc<InnerStarkConfig>,
        fri_verifier_params: FriVerifierParams,
    }

    impl core::ops::Deref for DreggRecursionConfig {
        type Target = InnerStarkConfig;
        fn deref(&self) -> &InnerStarkConfig {
            &self.config
        }
    }

    impl StarkGenericConfig for DreggRecursionConfig {
        type Challenge = Challenge;
        type Challenger = Challenger;
        type Pcs = MyPcs;

        fn pcs(&self) -> &MyPcs {
            self.config.pcs()
        }

        fn initialise_challenger(&self) -> Challenger {
            self.config.initialise_challenger()
        }
    }

    impl FriRecursionConfig for DreggRecursionConfig
    where
        MyPcs: p3_recursion::traits::RecursivePcs<
                DreggRecursionConfig,
                InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
                InnerFri,
                MerkleCapTargets<F, DIGEST_ELEMS>,
                <MyPcs as Pcs<Challenge, Challenger>>::Domain,
            >,
    {
        type Commitment = MerkleCapTargets<F, DIGEST_ELEMS>;
        type InputProof =
            InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>;
        type OpeningProof = InnerFri;
        type RawOpeningProof = <MyPcs as Pcs<Challenge, Challenger>>::Proof;
        const DIGEST_ELEMS: usize = DIGEST_ELEMS;

        fn with_fri_opening_proof<'a, A, R>(
            prev: &RecursionInput<'a, Self, A>,
            f: impl FnOnce(&Self::RawOpeningProof) -> R,
        ) -> R
        where
            A: RecursiveAir<Val<Self>, Self::Challenge, LogUpGadget>,
        {
            match prev {
                RecursionInput::UniStark { proof, .. } => f(&proof.opening_proof),
                RecursionInput::BatchStark { proof, .. } => f(&proof.proof.opening_proof),
                RecursionInput::NativeBatchStark { proof, .. } => f(&proof.opening_proof),
            }
        }

        fn prepare_circuit_for_verification(
            &self,
            circuit: &mut CircuitBuilder<Challenge>,
        ) -> Result<(), p3_recursion::verifier::VerificationError> {
            use p3_baby_bear::default_babybear_poseidon2_24;
            use p3_circuit::ops::generate_poseidon2_trace;
            use p3_poseidon2_circuit_air::{BabyBearD4Width16, BabyBearD4Width24};

            let perm = default_babybear_poseidon2_16();
            circuit.enable_poseidon2_perm::<BabyBearD4Width16, _>(
                generate_poseidon2_trace::<Challenge, BabyBearD4Width16>,
                perm,
            );
            // The ISOLATED segment-digest permutation: a SECOND Poseidon2 op-type
            // (`poseidon2_perm/baby_bear_d4_w24`) that shares neither chain-state, CTL bus,
            // nor (because its op-type and width differ) the connect/CSE collapse the FRI
            // challenger's width-16 perm participates in. The ordered-history segment digest
            // (`seg_poseidon_commit`) runs over THIS op so its perm I/O can never be aliased
            // into the verifier's `ExprId::ZERO` witness class.
            circuit.enable_poseidon2_perm_width_24::<BabyBearD4Width24, _>(
                generate_poseidon2_trace::<Challenge, BabyBearD4Width24>,
                default_babybear_poseidon2_24(),
            );
            circuit
                .enable_recompose::<F>(p3_circuit::ops::generate_recompose_trace::<F, Challenge>);
            circuit.enable_expose_claim::<F>(
                p3_circuit::ops::generate_expose_claim_trace::<F, Challenge>,
            );
            Ok(())
        }

        fn pcs_verifier_params(
            &self,
        ) -> &<MyPcs as p3_recursion::traits::RecursivePcs<
            DreggRecursionConfig,
            InputProofTargets<F, Challenge, RecValMmcs<F, DIGEST_ELEMS, MyHash, MyCompress>>,
            InnerFri,
            MerkleCapTargets<F, DIGEST_ELEMS>,
            <MyPcs as Pcs<Challenge, Challenger>>::Domain,
        >>::VerifierParams {
            &self.fri_verifier_params
        }

        fn set_fri_private_data(
            runner: &mut CircuitRunner<'_, Challenge>,
            op_ids: &[NonPrimitiveOpId],
            opening_proof: &Self::RawOpeningProof,
        ) -> Result<(), &'static str> {
            set_fri_mmcs_private_data::<
                F,
                Challenge,
                ChallengeMmcs,
                MyMmcs,
                MyHash,
                MyCompress,
                DIGEST_ELEMS,
            >(
                runner,
                op_ids,
                opening_proof,
                Poseidon2Config::BABY_BEAR_D4_W16,
            )
        }
    }

    // ========================================================================
    // Public API
    // ========================================================================

    /// Create the recursion-compatible STARK config.
    ///
    /// Uses Poseidon2 width-16 for all hash operations and the Duplex challenger.
    /// FRI parameters: log_blowup=3 (for degree-7 AIR), max_log_arity=1,
    /// 38 queries + 14 query-PoW bits.
    ///
    /// Security: conjectured (ethSTARK capacity bound) soundness is
    /// `log_blowup * num_queries + query_pow_bits = 3*38 + 14 = 128 bits` —
    /// the same bar the per-turn production config (`create_config`: q=50,
    /// pow=16, ~166 bits) clears, applied to the artifact a light client
    /// actually keeps. Every proof in the recursion tree — leaf wraps,
    /// aggregation layers, and the ROOT — runs at this strength, and the
    /// in-circuit FRI verifier re-verifies all 38 queries (plus the PoW
    /// witness, via `check_pow_witness`) of every wrapped child.
    pub fn create_recursion_config() -> DreggRecursionConfig {
        // Fixed knobs ⇒ identical config on every call; build once per thread, clone on access
        // (the config is `Arc`-backed, so a clone is an Arc bump + small param copy). `thread_local`
        // sidesteps any `Sync` requirement. The cached value is identical to a fresh build.
        thread_local! {
            static RECURSION_CONFIG: DreggRecursionConfig = create_recursion_config_uncached();
        }
        RECURSION_CONFIG.with(|c| c.clone())
    }

    fn create_recursion_config_uncached() -> DreggRecursionConfig {
        let perm = default_babybear_poseidon2_16();
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        // cap_height=0: single root digest. This is required because with small traces
        // (e.g. 4 rows -> tree depth 2), a larger cap_height would exceed tree depth.
        // The recursion library derives cap structure from the proof, so cap_height=0
        // gives the most compatible behavior.
        let val_mmcs = MyMmcs::new(hash, compress, 0);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        // log_blowup must be >= 3 because our AIR has degree-7 constraints (x^7 S-box).
        // With degree d=7 and blowup B, the quotient domain needs B >= d-1 = 6, so log_blowup >= 3.
        let fri_params = FriParameters {
            log_blowup: RECURSION_FRI_LOG_BLOWUP,
            log_final_poly_len: RECURSION_FRI_LOG_FINAL_POLY_LEN,
            max_log_arity: RECURSION_FRI_MAX_LOG_ARITY,
            num_queries: RECURSION_FRI_NUM_QUERIES,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: RECURSION_FRI_QUERY_POW_BITS,
            mmcs: challenge_mmcs,
        };
        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri_params);
        let challenger = Challenger::new(perm);
        let config = StarkConfig::new(pcs, challenger);

        use p3_circuit::ops::PermConfig;
        let fri_verifier_params = FriVerifierParams::with_mmcs(
            3,  // log_blowup (match prover)
            0,  // log_final_poly_len
            0,  // commit_pow_bits (match prover)
            14, // query_pow_bits (match prover)
            PermConfig::poseidon2(Poseidon2Config::BABY_BEAR_D4_W16),
        );

        DreggRecursionConfig {
            config: Arc::new(config),
            fri_verifier_params,
        }
    }

    /// Create a recursion config whose IN-CIRCUIT FRI VERIFIER params match a
    /// caller-specified `(log_blowup, query_pow_bits)` — for verifying an INNER proof
    /// that was minted under a DIFFERENT FRI engine than the recursion config's own.
    ///
    /// The recursion PROVER side (the `StarkConfig` PCS that re-proves the verifier
    /// circuit, i.e. the leaf-wrap's OUTPUT) is unchanged from
    /// [`create_recursion_config`] (log_blowup=3, 38 queries) — only the
    /// [`FriVerifierParams`] (which drive the in-circuit FRI verification of the inner
    /// proof) are retargeted. `num_queries` and FRI folding arity are read from the
    /// inner proof structure in-circuit, so only `log_blowup` / `log_final_poly_len` /
    /// `commit_pow` / `query_pow` need matching here.
    ///
    /// This is the SIDESTEP seam (C3 PART 2a): the dregg IR-v2 descriptor batch
    /// (`ir2_config`: log_blowup=6, 19 queries, 16 query-PoW) is verified in-circuit by
    /// a recursion verifier whose `FriVerifierParams` are `(6, 0, 0, 16, Poseidon2)`,
    /// while the leaf-wrap emits a standard recursion-config (log_blowup=3) proof.
    pub fn create_recursion_config_for_inner_fri(
        inner_log_blowup: usize,
        inner_log_final_poly_len: usize,
        inner_commit_pow_bits: usize,
        inner_query_pow_bits: usize,
    ) -> DreggRecursionConfig {
        create_recursion_config_with_fri(
            inner_log_blowup,
            inner_log_final_poly_len,
            // max_log_arity: PROBE — `ir2_config` uses 3 (fold up to 8/step), but the recursion
            // in-circuit verifier's recompose path is exercised at arity 1 (fold by 2) in every
            // existing recursion test. Use arity 1 here to isolate whether higher-arity folding
            // is the obstruction; the in-circuit verifier reads the count/arity from the proof.
            //
            // ⚑ The PROBE has a MEASURED BIT PRICE, and it is a CREDIT here, not a cost: arity is a
            // soundness lever worth `log₂(m−1)` bits (`Dregg2.Circuit.FriArityTransfer`), so folding
            // by 2 instead of 8 at this log_blowup takes the per-fold posture from 109 bits UP to 112
            // (`FriLedgerSound.arity8_costs_seven_times_arity2_at_logBlowup6`). Whichever way this
            // PROBE resolves, it is a soundness decision as much as a performance one.
            INNER_FRI_MAX_LOG_ARITY,
            // num_queries: matches `ir2_config`'s security target at log_blowup 6 (19 → ~130
            // conjectured bits); the in-circuit verifier reads the count from the proof.
            INNER_FRI_NUM_QUERIES,
            inner_commit_pow_bits,
            inner_query_pow_bits,
        )
    }

    /// Build a recursion config with a FULLY self-consistent FRI engine at the given knobs —
    /// the StarkConfig PCS (which MINTS proofs: the inner batch AND the leaf-wrap output) and
    /// the `FriVerifierParams` (which VERIFY the inner proof in-circuit) are BOTH set to these
    /// knobs. Use this when the inner proof is minted under a non-default FRI engine and the
    /// whole leaf-wrap (mint + in-circuit verify + output) runs at one engine.
    ///
    /// Differs from [`create_recursion_config`] only in the FRI knobs; the MMCS hash /
    /// compress / challenger / field are identical (so a proof minted here is structurally a
    /// `BatchProof<DreggRecursionConfig>` the native-batch leaf-wrap consumes directly).
    pub fn create_recursion_config_with_fri(
        log_blowup: usize,
        log_final_poly_len: usize,
        max_log_arity: usize,
        num_queries: usize,
        commit_pow_bits: usize,
        query_pow_bits: usize,
    ) -> DreggRecursionConfig {
        let perm = default_babybear_poseidon2_16();
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        let val_mmcs = MyMmcs::new(hash, compress, 0);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let fri_params = FriParameters {
            log_blowup,
            log_final_poly_len,
            max_log_arity,
            num_queries,
            commit_proof_of_work_bits: commit_pow_bits,
            query_proof_of_work_bits: query_pow_bits,
            mmcs: challenge_mmcs,
        };
        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri_params);
        let challenger = Challenger::new(perm);
        let config = StarkConfig::new(pcs, challenger);

        use p3_circuit::ops::PermConfig;
        let fri_verifier_params = FriVerifierParams::with_mmcs(
            log_blowup,
            log_final_poly_len,
            commit_pow_bits,
            query_pow_bits,
            PermConfig::poseidon2(Poseidon2Config::BABY_BEAR_D4_W16),
        );

        DreggRecursionConfig {
            config: Arc::new(config),
            fri_verifier_params,
        }
    }

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

    /// Generate a recursion-compatible inner proof for `P3MerklePoseidon2Air`
    /// from a pre-built trace.
    ///
    /// Kept as a convenience for the Merkle-membership POC; new callers should
    /// prefer [`prove_inner_for_air`] which accepts any [`RecursableAir`].
    pub fn prove_for_recursion(
        trace: &[Vec<BabyBear>],
        public_inputs: &[BabyBear],
    ) -> RecursionCompatibleProof {
        let air = P3MerklePoseidon2Air;
        let matrix = trace_to_matrix(trace);
        prove_inner_for_air(&air, matrix, public_inputs)
    }

    /// Verify a recursion-compatible inner proof for `P3MerklePoseidon2Air`.
    pub fn verify_for_recursion(
        proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<(), String> {
        let air = P3MerklePoseidon2Air;
        verify_inner_for_air(&air, proof, public_inputs)
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

    /// Produce a recursive proof that verifies a `P3MerklePoseidon2Air` inner
    /// proof in-circuit. Kept for backwards-compatibility with the
    /// Merkle-membership tests; new callers should prefer
    /// [`prove_recursive_layer_for_air`].
    pub fn prove_recursive_layer(
        inner_proof: &RecursionCompatibleProof,
        public_inputs: &[BabyBear],
    ) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
        let air = P3MerklePoseidon2Air;
        prove_recursive_layer_for_air(&air, inner_proof, public_inputs)
    }

    /// Produce a recursive proof for any `RecursableAir` inner proof.
    ///
    /// This is the generalized core recursion entry point. The Effect VM AIR
    /// (via its `p3-air` bridge), the simpler `AggregationAir`, and the
    /// canonical `P3MerklePoseidon2Air` all flow through this single function.
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

    /// Verify a recursive proof output.
    pub fn verify_recursive_layer(
        output: &RecursionOutput<DreggRecursionConfig>,
    ) -> Result<(), String> {
        verify_recursive_batch_proof(&output.0)
    }

    // ========================================================================
    // VK fingerprint: pinning the verifier-reconstruction inputs.
    // ========================================================================

    /// A fingerprint of a recursive batch proof's **verifier-reconstruction
    /// inputs** — the closest thing the fork's proof format has to a verifying
    /// key. [`verify_recursive_batch_proof`] reconstructs the circuit table
    /// AIRs and the preprocessed binding **from the proof itself**
    /// (`table_packing`, `rows`, `alu_variant`, `ext_degree`, `w_binomial`,
    /// the non-primitive table manifest, and `stark_common` — whose
    /// `preprocessed.commitment` is the Merkle binding of the verifier
    /// circuit's static op-list). Left unpinned, "the root verifies" means
    /// only "*some* circuit's proof verifies": a from-scratch prover could
    /// aggregate a DIFFERENT circuit's proofs and present a root this
    /// verifier accepts.
    ///
    /// The fingerprint hashes exactly those reconstruction inputs (shape +
    /// preprocessed binding; runtime values are excluded), so an accepted
    /// proof whose fingerprint equals a trusted anchor is — under blake3
    /// collision resistance and the MMCS commitment binding — a proof of the
    /// SAME verifier-circuit structure the anchor was extracted from.
    ///
    /// ## What this does and does NOT pin (be precise)
    ///
    /// PINS: the root layer's circuit structure — its op-list (via the
    /// preprocessed commitment), table shapes, packing, lookups (derived from
    /// the rebuilt AIRs), and the non-primitive table manifest shape.
    ///
    /// Does NOT (cannot, harness-side) pin: the **child** proofs' circuit
    /// identity. The fork's aggregation circuit takes each child's
    /// preprocessed commitment as a runtime PUBLIC INPUT of the parent
    /// circuit (`MerkleCapTargets::new` → `alloc_public_input_array`), and
    /// circuit public-input VALUES live in the constraint-free `PublicAir`
    /// main trace, which `verify_all_tables` never checks against
    /// caller-supplied values. Pinning child identity through the root needs
    /// fork work — see the module docs of [`crate::ivc_turn_chain`] for the
    /// precise follow-up.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    pub struct RecursionVk(pub [u8; 32]);

    impl RecursionVk {
        /// Hex rendering for error messages.
        pub fn to_hex(&self) -> String {
            self.0.iter().map(|b| format!("{b:02x}")).collect()
        }
    }

    /// Compute the [`RecursionVk`] fingerprint of a recursive batch proof's
    /// verifier-reconstruction inputs. Deterministic in the circuit structure;
    /// independent of the witness content (two proofs of the same circuit
    /// shape over different data fingerprint identically — that is what makes
    /// it usable as a trust anchor).
    pub fn recursion_vk_fingerprint(
        proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    ) -> RecursionVk {
        fn ser<T: serde::Serialize>(h: &mut blake3::Hasher, label: &str, v: &T) {
            let bytes = postcard::to_allocvec(v).expect(
                "VK-material field must postcard-serialize (alloc serializer is infallible)",
            );
            h.update(label.as_bytes());
            h.update(&(bytes.len() as u64).to_le_bytes());
            h.update(&bytes);
        }

        let mut h = blake3::Hasher::new();
        h.update(b"dregg-recursion-vk-v1");

        // The shape fields verify_all_tables rebuilds the table AIRs from.
        ser(&mut h, "table_packing", &proof.table_packing);
        ser(&mut h, "rows", &proof.rows);
        ser(&mut h, "alu_variant", &proof.alu_variant);
        h.update(&[proof.alu_quintic_trinomial as u8]);
        h.update(&(proof.ext_degree as u64).to_le_bytes());
        ser(&mut h, "w_binomial", &proof.w_binomial);

        // Per-table degree bits (the FRI domain shape the verifier trusts).
        ser(&mut h, "degree_bits", &proof.proof.degree_bits);

        // Non-primitive table manifest SHAPE (op_type / rows / lanes /
        // variant). `entry.public_values` are runtime values the host
        // verifier passes through to `verify_batch` — excluded so the
        // fingerprint stays content-independent.
        h.update(&(proof.non_primitives.len() as u64).to_le_bytes());
        for entry in &proof.non_primitives {
            ser(&mut h, "npo_op_type", &entry.op_type);
            h.update(&(entry.rows as u64).to_le_bytes());
            h.update(&(entry.lanes as u64).to_le_bytes());
            ser(&mut h, "npo_air_variant", &entry.air_variant);
        }

        // The preprocessed binding — THE verifying-key core: the Merkle
        // commitment to the verifier circuit's static op-list columns, plus
        // the per-instance metadata the verifier interprets it with.
        match &proof.stark_common.preprocessed {
            None => {
                h.update(&[0u8]);
            }
            Some(gp) => {
                h.update(&[1u8]);
                ser(&mut h, "preprocessed_commitment", &gp.commitment);
                h.update(&(gp.instances.len() as u64).to_le_bytes());
                for inst in &gp.instances {
                    match inst {
                        None => {
                            h.update(&[0u8]);
                        }
                        Some(m) => {
                            h.update(&[1u8]);
                            h.update(&(m.matrix_index as u64).to_le_bytes());
                            h.update(&(m.width as u64).to_le_bytes());
                            h.update(&(m.degree_bits as u64).to_le_bytes());
                        }
                    }
                }
                ser(&mut h, "matrix_to_instance", &gp.matrix_to_instance);
            }
        }

        RecursionVk(*h.finalize().as_bytes())
    }

    /// Verify a recursive proof from just the inner `BatchStarkProof`.
    ///
    /// Useful when the proof was serialised by itself (the
    /// `Rc<CircuitProverData<SC>>` half of `RecursionOutput` is only
    /// needed for *chaining* the proof into another recursion layer, not
    /// for verifying it). Block 3's scope-2 recursive replay path uses
    /// this entrypoint with postcard-decoded bytes.
    pub fn verify_recursive_batch_proof(
        proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
    ) -> Result<(), String> {
        verify_recursive_batch_proof_with_config(proof, &create_recursion_config())
    }

    /// [`verify_recursive_batch_proof`] under an explicit recursion config — the proof must
    /// have been PRODUCED under the same config's FRI engine. Used by the rotated native-batch
    /// leaf-wrap, whose output proof is at the `ir2`-knob config (log_blowup 6) rather than the
    /// default recursion knobs (log_blowup 3).
    pub fn verify_recursive_batch_proof_with_config(
        proof: &p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>,
        config: &DreggRecursionConfig,
    ) -> Result<(), String> {
        let mut prover = BatchStarkProver::new(config.clone());
        // Register the NPO table provers that were used to produce the recursive proof.
        // The verifier needs these to interpret the non-primitive ops in the proof.
        prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
        // The ISOLATED segment-digest permutation table (`baby_bear_d4_w24`): a distinct
        // Poseidon2 op-type the IVC segment-digest sponge runs over, so its rows never share
        // the W16 challenger's chain-state / CTL bus / connect graph. The verifier must
        // register it to interpret the W24 `poseidon2_perm` ops a segment-bearing root carries.
        prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
        // split_coeff_tables = false because Poseidon2Config::D (4) == extension degree D (4)
        prover.register_recompose_table::<D>(false);
        // The exposed-claim channel: the root proof carries an `expose_claim` table.
        prover.register_expose_claim_table::<D>();
        prover
            .verify_all_tables(proof)
            .map_err(|e| format!("Recursive proof verification failed: {:?}", e))
    }

    /// Verify a recursive proof from postcard-serialised bytes.
    ///
    /// Convenience wrapper for the verifier side: decodes the
    /// `BatchStarkProof` then delegates to [`verify_recursive_batch_proof`].
    pub fn verify_recursive_layer_bytes(bytes: &[u8]) -> Result<(), String> {
        let proof: p3_circuit_prover::BatchStarkProof<DreggRecursionConfig> =
            postcard::from_bytes(bytes)
                .map_err(|e| format!("Recursive proof postcard decode failed: {e}"))?;
        verify_recursive_batch_proof(&proof)
    }

    /// End-to-end: generate an inner Merkle membership proof, then prove it recursively.
    pub fn prove_recursive_membership(
        leaf_hash: BabyBear,
        siblings: &[[BabyBear; 3]],
        positions: &[u8],
    ) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
        let (trace, public_inputs) = generate_sound_merkle_trace(leaf_hash, siblings, positions);
        let inner_proof = prove_for_recursion(&trace, &public_inputs);
        verify_for_recursion(&inner_proof, &public_inputs)?;
        prove_recursive_layer(&inner_proof, &public_inputs)
    }

    // ========================================================================
    // Tests
    // ========================================================================

    #[cfg(test)]
    mod tests {
        use super::*;
        use dregg_circuit::poseidon2_air::create_poseidon2_test_witness;

        #[test]
        fn inner_proof_recursion_compatible() {
            let leaf = BabyBear::new(42424242);
            let witness = create_poseidon2_test_witness(leaf, 4);

            let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
            let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

            let (trace, public_inputs) = generate_sound_merkle_trace(leaf, &siblings, &positions);
            let proof = prove_for_recursion(&trace, &public_inputs);
            let result = verify_for_recursion(&proof, &public_inputs);
            assert!(
                result.is_ok(),
                "Recursion-compatible inner proof failed: {:?}",
                result.err()
            );
        }

        /// Block 1 (Kimchi survey § 9.1 starter task): demonstrate that the
        /// recursion path is not bound to `P3MerklePoseidon2Air`. Take the
        /// smallest other `Air`-implementing AIR in the crate
        /// (`AggregationAir`, width 4, degree 1, 2 public inputs — the
        /// minimum-non-trivial shape we have) and run it through the same
        /// `prove_inner_for_air` / `prove_recursive_layer_for_air`
        /// machinery. If this passes, the blanket `RecursiveAir` impl in
        /// `p3-recursion` accepts a column count + constraint set that
        /// differ from the Merkle POC, which is the *mechanical
        /// generalization* the survey asked us to measure.
        ///
        /// Block 1 outcome: clean acceptance (no fork changes required) —
        /// the `RecursableAir` trait alias captures exactly the bounds the
        /// fork's blanket impl needs, and any AIR implementing the standard
        /// `p3-air::Air<AB>` family flows through unmodified.
        #[test]
        fn recursive_aggregation_air_smoke() {
            use dregg_circuit::plonky3_recursion::AggregationAir;
            use p3_field::PrimeCharacteristicRing;
            use p3_matrix::dense::RowMajorMatrix;

            // Build a minimal aggregation trace by hand: 4 rows, width 4.
            // Row layout: [acc_in, leaf, root, acc_out].
            //
            // The AggregationAir constraints are:
            //   - first row: acc_in == pv[0]
            //   - last row: acc_out == pv[1]
            //   - transition: acc_out[i] == acc_in[i+1]
            //
            // We pick PI = [0, X] and a hand-rolled chain that satisfies the
            // transitions. The hash-chain computation is NOT enforced (this
            // is the recursion-shape smoke test, not the AggregationAir
            // soundness test — that lives in plonky3_recursion::tests).
            let pv0 = P3BabyBear::ZERO;
            let pv1 = P3BabyBear::from_u64(0xC0FFEE);
            let rows: Vec<[P3BabyBear; 4]> = vec![
                [
                    pv0,
                    P3BabyBear::from_u64(1),
                    P3BabyBear::from_u64(2),
                    P3BabyBear::from_u64(10),
                ],
                [
                    P3BabyBear::from_u64(10),
                    P3BabyBear::from_u64(3),
                    P3BabyBear::from_u64(4),
                    P3BabyBear::from_u64(20),
                ],
                [
                    P3BabyBear::from_u64(20),
                    P3BabyBear::from_u64(5),
                    P3BabyBear::from_u64(6),
                    P3BabyBear::from_u64(30),
                ],
                [
                    P3BabyBear::from_u64(30),
                    P3BabyBear::from_u64(7),
                    P3BabyBear::from_u64(8),
                    pv1,
                ],
            ];
            let flat: Vec<P3BabyBear> = rows.iter().flat_map(|r| r.iter().copied()).collect();
            let matrix = RowMajorMatrix::new(flat, 4);

            let pis_bb = vec![BabyBear::ZERO, BabyBear::new(0xC0FFEE)];

            let air = AggregationAir;

            // Inner proof generation through the generalized path.
            let inner = prove_inner_for_air(&air, matrix, &pis_bb);
            verify_inner_for_air(&air, &inner, &pis_bb)
                .expect("AggregationAir inner proof must verify");

            // Recursive layer through the generalized path.
            let rec = prove_recursive_layer_for_air(&air, &inner, &pis_bb)
                .expect("AggregationAir recursive layer must prove");
            verify_recursive_layer(&rec).expect("AggregationAir recursive layer must verify");
        }

        /// Core POC: one layer of real in-circuit recursive STARK verification.
        #[test]
        fn recursive_merkle_poc() {
            let leaf = BabyBear::new(42424242);
            let witness = create_poseidon2_test_witness(leaf, 4);

            let siblings: Vec<[BabyBear; 3]> = witness.levels.iter().map(|l| l.siblings).collect();
            let positions: Vec<u8> = witness.levels.iter().map(|l| l.position).collect();

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
