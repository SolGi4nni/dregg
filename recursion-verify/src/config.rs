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
    mint: MintKnobs,
}

/// ⚑ The FRI knobs this config's PCS MINTS at, recorded so a gate or a measurement can READ what
/// the deployed prover runs rather than reconstruct it from constants that may not be the ones the
/// builder took. `p3_fri::TwoAdicFriPcs::fri` is `pub(crate)`, so without this the knobs are
/// unreadable from outside the crate that built them — and a soundness knob no gate can read is not
/// gated (the same hole `IR2_INNER_*` was made `pub` to close).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MintKnobs {
    /// LDE rate exponent. Multiplies EVERY committed cell of this layer's own trace.
    pub log_blowup: usize,
    /// Final-polynomial length exponent.
    pub log_final_poly_len: usize,
    /// Fold arity exponent (`1` = fold by 2).
    pub max_log_arity: usize,
    /// FRI query count.
    pub num_queries: usize,
    /// Commit-phase grinding bits.
    pub commit_pow_bits: usize,
    /// Query-phase grinding bits.
    pub query_pow_bits: usize,
}

impl MintKnobs {
    /// The capacity ledger this config is gated against: `log_blowup · num_queries + query_pow`.
    pub const fn capacity_bits(&self) -> usize {
        self.log_blowup * self.num_queries + self.query_pow_bits
    }
}

impl DreggRecursionConfig {
    /// The knobs this config's PCS mints at — this layer's OWN proof, not its child's.
    pub const fn mint_knobs(&self) -> &MintKnobs {
        &self.mint
    }

    /// ⚑ The knobs this config's IN-CIRCUIT verifier checks its CHILD against — the other half of
    /// the pair [`recursion_layer_over`] separates, `pub` for the same reason
    /// [`MintKnobs`] is: a gate that can only read the mint side cannot tell a config that moved
    /// its child's acceptance from one that did not. `(log_blowup, log_final_poly_len,
    /// commit_pow_bits, query_pow_bits)`; arity and query count come off the child's proof.
    pub const fn verify_knobs(&self) -> (usize, usize, usize, usize) {
        (
            self.fri_verifier_params.log_blowup,
            self.fri_verifier_params.log_final_poly_len,
            self.fri_verifier_params.commit_pow_bits,
            self.fri_verifier_params.query_pow_bits,
        )
    }
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
    create_recursion_config_split_fri(
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_pow_bits,
        query_pow_bits,
        log_blowup,
        log_final_poly_len,
        commit_pow_bits,
        query_pow_bits,
    )
}

/// ⚑⚑ **THE TWO ROLES, SEPARATED — they were never one knob set.**
///
/// A recursion layer holds TWO FRI engines and [`create_recursion_config_with_fri`] set both from
/// one argument list:
///
/// * the **MINT** engine — `StarkConfig`'s PCS, which LDEs and commits *this* layer's own trace.
///   `two_adic_pcs.rs:317` calls `coset_lde_batch(evals, self.fri.log_blowup, shift)`, so this
///   `log_blowup` multiplies every committed cell of the verification circuit.
/// * the **VERIFY** engine — `FriVerifierParams`, which the in-circuit verifier checks the CHILD's
///   proof against. This one is not a choice: it must equal the knobs the child was minted at.
///
/// Only the second is constrained. Tying the first to it makes the child's blowup the whole tower's
/// blowup: `ir2_config` mints the innermost descriptor batch at `log_blowup = 6`, and that 64×
/// propagated up through every leaf wrap and every fold, blowing up traces two orders of magnitude
/// larger than the descriptor's own. The child's engine is a fact about a proof that already
/// exists; the layer's own engine is a free choice, and its only real constraint is that the
/// PARENT's verify engine matches it.
///
/// ⚠ `mint_num_queries` and `mint_max_log_arity` have no verify-side twin here on purpose: the
/// in-circuit verifier reads the child's query count and folding arity from the child's proof
/// STRUCTURE, so only blowup / final-poly-len / the two PoW knobs need matching.
#[allow(clippy::too_many_arguments)]
pub fn create_recursion_config_split_fri(
    mint_log_blowup: usize,
    mint_log_final_poly_len: usize,
    mint_max_log_arity: usize,
    mint_num_queries: usize,
    mint_commit_pow_bits: usize,
    mint_query_pow_bits: usize,
    verify_log_blowup: usize,
    verify_log_final_poly_len: usize,
    verify_commit_pow_bits: usize,
    verify_query_pow_bits: usize,
) -> DreggRecursionConfig {
    let log_blowup = mint_log_blowup;
    let log_final_poly_len = mint_log_final_poly_len;
    let max_log_arity = mint_max_log_arity;
    let num_queries = mint_num_queries;
    let commit_pow_bits = mint_commit_pow_bits;
    let query_pow_bits = mint_query_pow_bits;
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
    // ⚑ THE IN-CIRCUIT VERIFIER PARAMS DESCRIBE THE CHILD, NOT THIS LAYER. They were inline
    // literals once, matching by coincidence; then they were tied to the minting knobs, which made
    // the child's engine this layer's engine. They are the child's engine and nothing else.
    let fri_verifier_params = FriVerifierParams::with_mmcs(
        verify_log_blowup,
        verify_log_final_poly_len,
        verify_commit_pow_bits,
        verify_query_pow_bits,
        PermConfig::poseidon2(Poseidon2Config::BABY_BEAR_D4_W16),
    );

    DreggRecursionConfig {
        config: Arc::new(config),
        fri_verifier_params,
        mint: MintKnobs {
            log_blowup,
            log_final_poly_len,
            max_log_arity,
            num_queries,
            commit_pow_bits,
            query_pow_bits,
        },
    }
}

/// ⚑ **THE ENGINE THE IR-v2 DESCRIPTOR BATCH IS MINTED AT** — `log_blowup 6 / 19 queries /
/// 16 query-PoW`, arity 2. A leaf wrap's in-circuit FRI verifier is retargeted to these knobs so
/// an `ir2_config` proof verifies as-is; pass this to a leaf, which derives its own minting engine
/// from it via [`recursion_layer_over`].
///
/// ⚠ **ITS NAME IS A HISTORICAL ARTEFACT AND ITS OLD DOC SENTENCE IS RETRACTED.** It read *"THE
/// CONFIG EVERY IR-v2 LEAF WRAP, FOLD AND ROOT VERIFY RUNS AT"*, and that was true only because a
/// leaf wrap used to inherit its child's minting engine and hand it to the whole tower — which is
/// the 64× this repricing removed. A leaf wrap now VERIFIES here and MINTS at
/// `create_recursion_config`'s engine, so **no fold and no root runs at this config any more**.
/// A consumer verifying a root wants the tower's root config
/// (`ivc_turn_chain::turn_chain_root_config`, `accumulator_root::accumulator_root_config`,
/// `chain_root::chain_root_config`), and the honest failure for taking this one instead is
/// `QueryProofCountMismatch { expected: 19, got: 38 }`.
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

/// ⚑⚑ **THE SAME LEAF WRAP, MINTING AT ITS OWN BLOWUP INSTEAD OF ITS CHILD'S.**
///
/// In-circuit VERIFY engine: the IR-v2 descriptor batch's (`log_blowup 6`, `query_pow 16`) — an
/// unchanged fact about the child proof, so the same `Ir2BatchProof` verifies with no re-mint.
/// MINT engine: [`create_recursion_config`]'s (`log_blowup 3`, arity 2, 38 queries, `query_pow`
/// 14) — the knob set every non-IR-v2 recursion layer in the workspace already runs at, whose
/// capacity ledger is `3·38 + 14 = 128`, against `ir2_leaf_wrap_config`'s `6·19 + 16 = 130`.
///
/// So the wrap's own committed LDE falls **8×** with no soundness knob moved down, and the child's
/// in-circuit verification is bit-for-bit the one that runs today.
///
/// ⚠ Its OUTPUT proof is at `log_blowup 3 / 38 queries`, so a parent that folds it must VERIFY at
/// those knobs — i.e. [`create_recursion_config`], not `ir2_leaf_wrap_config`. That is a VK/epoch
/// rotation of the recursion tree, not a descriptor re-emit: no AIR, trace or descriptor JSON
/// changes.
pub fn ir2_leaf_wrap_split_config() -> DreggRecursionConfig {
    thread_local! {
        static SPLIT_WRAP_CONFIG: DreggRecursionConfig = create_recursion_config_split_fri(
            RECURSION_FRI_LOG_BLOWUP,
            RECURSION_FRI_LOG_FINAL_POLY_LEN,
            RECURSION_FRI_MAX_LOG_ARITY,
            RECURSION_FRI_NUM_QUERIES,
            RECURSION_FRI_COMMIT_POW_BITS,
            RECURSION_FRI_QUERY_POW_BITS,
            IR2_INNER_LOG_BLOWUP,
            IR2_INNER_LOG_FINAL_POLY_LEN,
            IR2_INNER_COMMIT_POW_BITS,
            IR2_INNER_QUERY_POW_BITS,
        );
    }
    SPLIT_WRAP_CONFIG.with(|c| c.clone())
}

/// ⚑⚑ **THE ONE RULE THE WHOLE TOWER RUNS BY: a layer VERIFIES its child at the child's own
/// engine and MINTS at the recursion engine.**
///
/// Every recursion layer in this workspace used to be handed ONE config that played both roles,
/// which worked only because the two roles happened to coincide: an IR-v2 leaf wrap verified a
/// child minted at `(lb 6, q 19, qpow 16)` and minted its own output at those same knobs, so its
/// parent could verify it with the same object. The coincidence cost the tower 64× on every
/// committed cell of a verification circuit ~10^3 times larger than the descriptor it verifies.
///
/// This function is the coincidence, broken and then made structural. Given the config a child
/// proof was MINTED under, it returns the config the layer ABOVE that child must run at:
///
/// * **verify engine** = `child.mint_knobs()`, exactly — so the in-circuit verification of that
///   child is bit-for-bit the one that ran before and **no child proof's acceptance moves**;
/// * **mint engine** = [`create_recursion_config`]'s `(lb 3, arity 2, q 38, qpow 14)`, the knob
///   set every non-IR-v2 recursion layer already runs at.
///
/// ⚑ **It has a FIXED POINT, and the fixed point is [`create_recursion_config`].** Over a child
/// minted at the IR-v2 descriptor engine it is [`ir2_leaf_wrap_split_config`] (the leaf wrap);
/// over anything minted at the recursion engine — which is what a leaf wrap now emits — it is
/// `create_recursion_config()` itself. So one rule generates the whole tower: leaf wrap, then
/// every fold and the root verify, and iterating it a second time changes nothing. Both facts are
/// theorems of this function rather than knobs someone remembers to pass:
/// `tests/tower_config_law.rs`.
///
/// ⚠ `max_log_arity` and `num_queries` are deliberately absent from the verify side: the
/// in-circuit verifier reads a child's folding arity and query count off the child's proof
/// STRUCTURE, so only blowup / final-poly-len / the two PoW knobs need matching.
pub fn recursion_layer_over(child: &DreggRecursionConfig) -> DreggRecursionConfig {
    let k = child.mint_knobs();
    // Memoised on the four verify knobs: this is called once per leaf and once per fold, and the
    // Poseidon2 round constants + DFT twiddles behind a config are not free. `thread_local`
    // sidesteps any `Sync` requirement on the config, exactly as the fixed builders above do.
    thread_local! {
        static LAYERS: std::cell::RefCell<
            std::collections::HashMap<(usize, usize, usize, usize), DreggRecursionConfig>,
        > = std::cell::RefCell::new(std::collections::HashMap::new());
    }
    let key = (
        k.log_blowup,
        k.log_final_poly_len,
        k.commit_pow_bits,
        k.query_pow_bits,
    );
    LAYERS.with(|m| {
        m.borrow_mut()
            .entry(key)
            .or_insert_with(|| {
                create_recursion_config_split_fri(
                    RECURSION_FRI_LOG_BLOWUP,
                    RECURSION_FRI_LOG_FINAL_POLY_LEN,
                    RECURSION_FRI_MAX_LOG_ARITY,
                    RECURSION_FRI_NUM_QUERIES,
                    RECURSION_FRI_COMMIT_POW_BITS,
                    RECURSION_FRI_QUERY_POW_BITS,
                    key.0,
                    key.1,
                    key.2,
                    key.3,
                )
            })
            .clone()
    })
}

/// ⚑⚑ **THE ONE OBJECT AT THE TOP OF EVERY IR-v2 RECURSION TOWER** — the config every fold node
/// above a leaf mints at, every root is minted at, and every native root verify runs at.
///
/// It is [`recursion_layer_over`]'s fixed point reached from the IR-v2 descriptor engine: leaf
/// wrap, then the layer above that, and no further. Every tower-specific accessor
/// (`ivc_turn_chain::turn_chain_root_config`, [`crate::accumulator_root::accumulator_root_config`])
/// **delegates here rather than recomputing** — a prove-side and a verify-side answer to "what
/// config is a root at" that agree today are two answers that disagree the first time one is
/// retuned, and both sides would still BUILD; only the FRI would refuse.
///
/// ⚠ It is not a new posture: it is `create_recursion_config()`, the knob set every non-IR-v2
/// recursion layer in this workspace already ran at.
pub fn recursion_tower_root_config() -> DreggRecursionConfig {
    recursion_layer_over(&recursion_layer_over(&ir2_leaf_wrap_config()))
}
