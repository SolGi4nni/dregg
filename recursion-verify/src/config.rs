//! The recursion STARK config — **the one object**, not a verify-side copy of it.
//!
//! `DreggRecursionConfig` used to live in `dregg-circuit-prove`, which meant a consumer that
//! wanted to VERIFY a recursion root had to link the whole prove tower to name the type its
//! proof is parameterised by. Moving the type here inverts that: `dregg-circuit-prove` now
//! depends on this crate and re-exports these items from
//! `plonky3_recursion_impl::recursive`, so every path that named them still resolves and there
//! is exactly ONE `DreggRecursionConfig` in the workspace.
//!
//! ⚠ A verify-side TWIN of this config would have been cheaper to write and is the thing to
//! refuse: two `StarkConfig`s that agree on FRI knobs today are two configs that disagree the
//! first time one is retuned, and the symptom is a proof that "verifies" under a config the
//! prover does not run. The `FriRecursionConfig` impl below is why the move (rather than a
//! copy) was forced — the orphan rule puts it in the crate that owns the type.

use std::sync::Arc;

use p3_baby_bear::{BabyBear as P3BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_circuit::{CircuitBuilder, CircuitRunner, NonPrimitiveOpId};
use p3_commit::{ExtensionMmcs, Pcs};
use p3_dft::Radix2DitParallel;
use p3_field::Field;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_lookup::logup::LogUpGadget;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_recursion::pcs::{
    InputProofTargets, MerkleCapTargets, RecValMmcs, set_fri_mmcs_private_data,
};
use p3_recursion::traits::RecursiveAir;
use p3_recursion::{FriVerifierParams, RecursionInput, ops::Poseidon2Config};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{Proof, StarkConfig, StarkGenericConfig, Val};

/// The challenge extension degree — `|F| = babyBearP ^ 4 ≈ 2^123.6`, the denominator of every
/// per-fold proximity-gap bound.
pub const RECURSION_EXT_DEGREE: usize = 4;

/// The extension degree as the `D` const generic every recursion entry point is instantiated at.
pub const D: usize = RECURSION_EXT_DEGREE;
/// Poseidon2 permutation width.
pub const WIDTH: usize = 16;
/// Poseidon2 sponge rate.
pub const RATE: usize = 8;
/// Digest width in base-field elements.
pub const DIGEST_ELEMS: usize = 8;

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
/// [`create_recursion_config`]'s FRI **commit-phase** proof-of-work bits — plonky3's second
/// grinding knob (`fri/src/config.rs:18`), ground per fold round after the round commitment is
/// observed and before the folding challenge `β` is drawn (`fri/src/prover.rs:224`, checked
/// `verifier.rs:222`). It is the only lever on the `ε_C` branch that is not a field-extension
/// flag day (`Dregg2.Circuit.FriCommitPow.commit_pow_moves_the_commit_branch`), and it is
/// **hard-capped at 30 bits** by `grind`'s `assert!((1u64 << bits) < F::ORDER_U64)` over a
/// single BabyBear witness (`FriCommitPow.maxGrindBits_is_the_babybear_witness_cap`).
pub const RECURSION_FRI_COMMIT_POW_BITS: usize = 0;
/// [`create_recursion_config`]'s FRI fold arity exponent — 1, i.e. fold by 2.
pub const RECURSION_FRI_MAX_LOG_ARITY: usize = 1;
/// [`create_recursion_config`]'s FRI final-polynomial length exponent — 0 (constant final poly).
pub const RECURSION_FRI_LOG_FINAL_POLY_LEN: usize = 0;

/// The fold arity exponent [`create_recursion_config_for_inner_fri`] pins — **1 (fold by 2)**,
/// the knob that makes [`ir2_leaf_wrap_config`] an ARITY-2 config even though `ir2_config`
/// (which it otherwise matches) is arity 8.
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

/// ⚑ The IR-v2 leaf-wrap inner-FRI knobs. `pub` so the params gate can read the constants the
/// deployed config ACTUALLY reads rather than reconstructing the row from other constants.
pub const IR2_INNER_LOG_BLOWUP: usize = 6;
/// The leaf-wrap inner FRI final-polynomial length exponent.
pub const IR2_INNER_LOG_FINAL_POLY_LEN: usize = 0;
/// The leaf-wrap inner FRI **commit-phase** PoW bits — the `Dregg2.Circuit.FriCommitPow` lever,
/// the only one on that branch which binds at this exact config without a field-extension flag
/// day. Capped at 30 by `grind`'s single-BabyBear-witness assertion.
pub const IR2_INNER_COMMIT_POW_BITS: usize = 0;
/// The leaf-wrap inner FRI query PoW bits.
pub const IR2_INNER_QUERY_POW_BITS: usize = 16;

/// The recursion base field.
pub type F = P3BabyBear;
/// The degree-4 challenge extension.
pub type Challenge = BinomialExtensionField<F, D>;
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
/// The duplex challenger the whole tower runs on.
pub type Challenger = DuplexChallenger<F, Perm, WIDTH, RATE>;
/// The FRI PCS.
pub type MyPcs = TwoAdicFriPcs<F, Dft, MyMmcs, ChallengeMmcs>;

/// The raw STARK config type (without the FRI verifier-params wrapper).
pub type InnerStarkConfig = StarkConfig<MyPcs, Challenge, Challenger>;

/// The proof type produced by the recursion-compatible prover.
pub type RecursionCompatibleProof = Proof<DreggRecursionConfig>;

/// FRI proof targets for the in-circuit verifier.
pub type InnerFri = p3_recursion::pcs::FriProofTargets<
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

/// Wrapper around the STARK config that adds FRI verifier params.
///
/// Implements both `StarkGenericConfig` (by delegation) and `FriRecursionConfig` (required by
/// the recursion backend). **The `FriRecursionConfig` impl is why this type lives in this crate
/// rather than in a verify-side twin:** the trait is foreign, so the impl must sit with the type.
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

impl p3_recursion::FriRecursionConfig for DreggRecursionConfig
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
        // challenger's width-16 perm participates in.
        circuit.enable_poseidon2_perm_width_24::<BabyBearD4Width24, _>(
            generate_poseidon2_trace::<Challenge, BabyBearD4Width24>,
            default_babybear_poseidon2_24(),
        );
        circuit.enable_recompose::<F>(p3_circuit::ops::generate_recompose_trace::<F, Challenge>);
        circuit
            .enable_expose_claim::<F>(p3_circuit::ops::generate_expose_claim_trace::<F, Challenge>);
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

/// Create the recursion-compatible STARK config.
///
/// ⚠ **The `128` this config is often quoted at is the REFUTED capacity column, and it is not a
/// security number.** `log_blowup * num_queries + query_pow_bits = 3*38 + 14 = 128` is the
/// up-to-`(1−ρ)` arithmetic whose correlated-agreement conjecture is disproved (Crites–Stewart,
/// eprint 2025/2046; Kambiré, arXiv 2604.09724). It is carried as a knob-drift baseline ONLY —
/// and this config sits at EXACTLY the `128` drift margin with ZERO headroom, so any knob move
/// down is a red gate.
///
/// The honest columns for this config, all from the Lean ledger (`Dregg2.Circuit.FriLedger`):
/// * **Johnson query column: `71`** — `38*3/2 + 14`; the WEAKEST shipped config on both query
///   columns, so it pins the gate's Johnson floor.
/// * **per-fold: `118`** — at the NEAR-CAPACITY radius, not at the Johnson radius FRI operates
///   at (`Dregg2.Circuit.FriJohnsonRadiusGap`).
pub fn create_recursion_config() -> DreggRecursionConfig {
    // Fixed knobs ⇒ identical config on every call; build once per thread, clone on access
    // (the config is `Arc`-backed). `thread_local` sidesteps any `Sync` requirement.
    thread_local! {
        static RECURSION_CONFIG: DreggRecursionConfig = create_recursion_config_uncached();
    }
    RECURSION_CONFIG.with(|c| c.clone())
}

fn create_recursion_config_uncached() -> DreggRecursionConfig {
    create_recursion_config_with_fri(
        RECURSION_FRI_LOG_BLOWUP,
        RECURSION_FRI_LOG_FINAL_POLY_LEN,
        RECURSION_FRI_MAX_LOG_ARITY,
        RECURSION_FRI_NUM_QUERIES,
        RECURSION_FRI_COMMIT_POW_BITS,
        RECURSION_FRI_QUERY_POW_BITS,
    )
}

/// Create a recursion config whose IN-CIRCUIT FRI VERIFIER params match a caller-specified
/// `(log_blowup, query_pow_bits)` — for verifying an INNER proof that was minted under a
/// DIFFERENT FRI engine than the recursion config's own.
///
/// `num_queries` and FRI folding arity are read from the inner proof structure in-circuit, so
/// only `log_blowup` / `log_final_poly_len` / `commit_pow` / `query_pow` need matching here.
pub fn create_recursion_config_for_inner_fri(
    inner_log_blowup: usize,
    inner_log_final_poly_len: usize,
    inner_commit_pow_bits: usize,
    inner_query_pow_bits: usize,
) -> DreggRecursionConfig {
    create_recursion_config_with_fri(
        inner_log_blowup,
        inner_log_final_poly_len,
        // ⚑ arity is a soundness lever worth `log₂(m−1)` bits (`Dregg2.Circuit.FriArityTransfer`):
        // folding by 2 instead of 8 at this log_blowup takes the per-fold posture from 109 bits UP
        // to 112 (`FriLedgerSound.arity8_costs_seven_times_arity2_at_logBlowup6`).
        INNER_FRI_MAX_LOG_ARITY,
        INNER_FRI_NUM_QUERIES,
        inner_commit_pow_bits,
        inner_query_pow_bits,
    )
}

/// Build a recursion config with a FULLY self-consistent FRI engine at the given knobs — the
/// StarkConfig PCS (which MINTS proofs) and the `FriVerifierParams` (which VERIFY the inner
/// proof in-circuit) are BOTH set to these knobs.
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
    // cap_height=0: single root digest. With small traces a larger cap_height would exceed tree
    // depth; the recursion library derives cap structure from the proof.
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
    // ⚑ THE IN-CIRCUIT VERIFIER PARAMS READ THE SAME ARGUMENTS THE PROVER'S `FriParameters` DID.
    // They were inline literals once, matching by coincidence; a knob move would have left the
    // in-circuit verifier checking a config the prover does not run.
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

/// ⚑ **THE CONFIG EVERY IR-v2 LEAF WRAP, FOLD AND ROOT VERIFY RUNS AT.** The inner descriptor
/// batch is minted at log_blowup 6 / 19 queries / 16 query-PoW, so the wrap's in-circuit FRI
/// verifier must be retargeted to those knobs — verifying a root under
/// [`create_recursion_config`] instead simply fails, which is the honest failure mode but a
/// confusing one, so callers should take this function rather than assemble knobs.
pub fn ir2_leaf_wrap_config() -> DreggRecursionConfig {
    thread_local! {
        static LEAF_WRAP_CONFIG: DreggRecursionConfig = create_recursion_config_for_inner_fri(
            IR2_INNER_LOG_BLOWUP,
            IR2_INNER_LOG_FINAL_POLY_LEN,
            IR2_INNER_COMMIT_POW_BITS,
            IR2_INNER_QUERY_POW_BITS,
        );
    }
    LEAF_WRAP_CONFIG.with(|c| c.clone())
}
