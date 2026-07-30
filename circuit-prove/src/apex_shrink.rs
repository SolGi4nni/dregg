//! THE SHRINK LAYER: the apex-verifier AIR proven under [`DreggOuterConfig`].
//!
//! This is the capstone of the BN254-native-hash wrap re-architecture
//! (docs/deos/WRAP-NATIVE-HASH-DECISION.md): take a real `ir2_leaf_wrap` apex
//! proof (the root `BatchStarkProof<DreggRecursionConfig>` a turn-chain fold
//! produces — BabyBear Poseidon2-W16 commitments and transcript), verify it
//! IN-CIRCUIT with the field-generic p3-recursion verifier, and prove THAT
//! circuit under the outer config — BN254-native Merkle roots and a
//! BN254-native (MultiField) Fiat–Shamir transcript. The resulting SHRINK
//! PROOF is the object `chain/gnark/fri_verify_native.go` hashes natively:
//! one ~243-R1CS `Poseidon2Bn254Compress` per Merkle level instead of one
//! ~16,837-R1CS emulated BabyBear permutation (the measured 40.9M → 1.0M
//! collapse of the wrap's hashing term).
//!
//! ## How the two configs split (the instantiation the module doc of
//! [`crate::dregg_outer_config`] names)
//!
//! The fork's one-config pipeline (`build_and_prove_next_layer`) uses a single
//! `SC` for BOTH roles: the inner proof being verified in-circuit AND the
//! prover of the next layer. The shrink layer needs those roles SPLIT:
//!
//! | role | config | why |
//! |---|---|---|
//! | circuit build + in-circuit verify + witness gen | [`DreggRecursionConfig`] (`ir2_leaf_wrap_config`) | the apex's commitments/transcript are BabyBear-hash; `FriRecursionConfig` (verifier params, FRI private data) must match the proof being verified |
//! | table commit + FRI + transcript of the SHRINK proof | [`DreggOuterConfig`] | the OUTPUT must be BN254-native for gnark |
//!
//! The split is sound because the two configs share `Val = BabyBear` and
//! `Challenge = EF4`: the verifier circuit is a field-level object
//! (`Circuit<EF4>`), its table AIRs depend only on `Val`/`Challenge`, and
//! only the PCS/challenger — swapped wholesale via the outer config — touch
//! the hash field. Concretely this module re-plays `prove_next_layer`'s five
//! steps with the config swapped at the field-compatible seam:
//!
//! 1. `build_next_layer_circuit::<DreggRecursionConfig, ..>` — the apex-verifier
//!    circuit (in-circuit FRI verify of the apex at the `ir2` knobs: 19 queries,
//!    log_blowup 6, 16 query-PoW bits, Poseidon2-W16 + W24 + recompose +
//!    expose_claim non-primitive ops).
//! 2. `get_airs_and_degrees_with_prep::<DreggOuterConfig, ..>` — the SAME table
//!    AIRs, typed at the outer config (`CircuitTableAir<SC, D>` uses SC only via
//!    `Val`/`Challenge`).
//! 3. Witness generation — runner + the INNER config's FRI private data
//!    (`set_fri_private_data` injects the apex's BabyBear Merkle siblings).
//! 4. `ProverData::from_airs_and_degrees(&outer, ..)` — the preprocessed
//!    (op-list) commitment, now a BN254-native Merkle root.
//! 5. `BatchStarkProver::<DreggOuterConfig>::prove_all_tables` — the shrink proof.
//!
//! ## What the shrink proof attests
//!
//! `verify_shrink_proof` accepting means: a circuit whose constraints encode
//! "the apex batch proof verifies under `ir2_leaf_wrap_config`" is satisfied —
//! with the SAME soundness caveat every recursion layer in this tree carries
//! (see [`crate::plonky3_recursion_impl::recursive::RecursionVk`]): the shrink
//! proof's preprocessed commitment pins the verifier-circuit structure, and
//! the apex's own preprocessed commitment rides as public inputs of the shrink
//! circuit. Chain-level binding (which apex, which VK) is the same
//! fingerprint/anchor discipline the BabyBear tree already uses.
//!
//! ## HONEST SCOPE / named residual
//!
//! Landed here: the split-config instantiation + real-apex shrink + Rust-side
//! verify (see `tests/apex_shrink_bn254_tooth.rs`), and the gnark-side fixture
//! export ([`crate::apex_shrink_gnark_export`], test
//! `tests/apex_shrink_gnark_fixture.rs`): the shrink proof's FRI opening data
//! (commit roots, final poly, PoW witness, per-query openings + reduced
//! openings) plus the full pre-FRI transcript event log, which
//! `chain/gnark`'s `VerifyFriNative` verifies against the REAL transcript
//! (fixture `chain/gnark/fixtures/apex_shrink_fri_real.json`). The NAMED
//! residual on the gnark side is the full batch-STARK verify — in-circuit
//! input batch openings + alpha reduction, constraint evaluation at zeta,
//! quotient recomposition — and then the Groth16 wrap of that circuit (see
//! the HONEST SCOPE in `apex_shrink_gnark_export.rs` and
//! `chain/gnark/fri_verify_native.go`).

use std::rc::Rc;

use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::ProverData;
use p3_circuit_prover::{
    AirVariant, BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile,
    TablePacking,
    common::{NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep},
    expose_claim_air_builders, expose_claim_preprocessor, poseidon2_air_builders,
    poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
};
use p3_commit::{Pcs as P3Pcs, PolynomialSpace};
use p3_field::extension::BinomialExtensionField;
use p3_lookup::logup::LogUpGadget;
use p3_recursion::traits::RecursiveAir;
use p3_recursion::{
    BatchOnly, PcsRecursionBackend, ProveNextLayerParams, RecursionInput, RecursionOutput,
    VerifierCircuitResult, build_next_layer_circuit, ops::Poseidon2Config,
};
use p3_uni_stark::StarkGenericConfig;

use crate::dregg_outer_config::DreggOuterConfig;
use crate::plonky3_recursion_impl::recursive::{DreggRecursionConfig, create_recursion_backend};

/// Extension degree — must match both configs' `Challenge = EF4`.
const D: usize = 4;
/// The circuit/trace element field (both configs' `Challenge`).
type EF = BinomialExtensionField<P3BabyBear, D>;

/// A BN254-native-hash shrink proof: the apex-verifier circuit's batch proof
/// under [`DreggOuterConfig`], plus the prover data whose
/// `stark_common.preprocessed` is the shrink circuit's VK core (a BN254-native
/// Merkle commitment to the verifier circuit's static op-list).
pub struct ApexShrinkProof<SC: OuterShrinkConfig = DreggOuterConfig> {
    /// The shrink proof itself — outer-field commitments, MultiField transcript.
    pub proof: BatchStarkProof<SC>,
    /// Prover-side data (preprocessed binding etc.). Kept for VK extraction /
    /// re-proving; NOT needed by [`verify_shrink_proof`] (the proof carries its
    /// own `stark_common`).
    pub prover_data: Rc<CircuitProverData<SC>>,
}

/// The bound an OUTER config must satisfy to sit in the shrink's second role.
///
/// ⚑ **This is the seam the module doc argues is sound, written as a trait
/// bound instead of a paragraph.** The split works because the two configs
/// share `Val = BabyBear` and `Challenge = EF4`: the verifier circuit is a
/// field-level object (`Circuit<EF4>`), its table AIRs depend only on
/// `Val`/`Challenge`, and only the PCS/challenger — swapped wholesale — touch
/// the hash field. A config that did NOT share those two cannot be named here,
/// so the seam cannot be widened by accident.
///
/// Two configs satisfy it today:
/// [`DreggOuterConfig`] (Poseidon2-BN254, the ETH terminal) and
/// [`crate::dregg_mina_config::DreggMinaConfig`] (Mina-Poseidon over Pasta, the
/// Mina terminal). Adding a third destination chain is a config, not a change
/// here.
pub trait OuterShrinkConfig:
    StarkGenericConfig<
        Challenge = EF,
        Pcs: P3Pcs<EF, Self::Challenger, Domain: PolynomialSpace<Val = P3BabyBear>>,
    >
    + 'static
    + Send
    + Sync
{
}

impl<SC> OuterShrinkConfig for SC where
    SC: StarkGenericConfig<
            Challenge = EF,
            Pcs: P3Pcs<EF, SC::Challenger, Domain: PolynomialSpace<Val = P3BabyBear>>,
        >
        + 'static
        + Send
        + Sync
{
}

/// Shrink a REAL apex — the root [`RecursionOutput`] of a turn-chain fold
/// (e.g. [`crate::ivc_turn_chain::WholeChainProof::root`]) — into a
/// BN254-native-hash proof under `outer_config`.
///
/// `inner_config` must be the config the apex was minted under
/// ([`crate::ivc_turn_chain::ir2_leaf_wrap_config`] for the rotated fold): its
/// `FriVerifierParams` drive the in-circuit re-verification of all 19 FRI
/// queries (+ the 16-bit PoW witness) of the apex.
pub fn shrink_apex_to_outer<SC: OuterShrinkConfig>(
    apex: &RecursionOutput<DreggRecursionConfig>,
    inner_config: &DreggRecursionConfig,
    outer_config: &SC,
) -> Result<ApexShrinkProof<SC>, String> {
    let input = apex.into_recursion_input::<BatchOnly>();
    shrink_recursion_input_to_outer(&input, inner_config, outer_config)
}

/// The default TablePacking the shrink proves at — the byte-for-byte packing
/// `prove_next_layer` uses (`ProveNextLayerParams::default().table_packing`:
/// public_lanes 1, alu_lanes 4, horner_packed_steps 2, all NPO lanes 1). The
/// `_with_packing` entrypoints below let a caller retarget it; passing THIS is
/// identical to the parameterless path.
///
/// See docs/deos/APEX-VERIFIER-AIR-REDUCTION.md: the ALU table (the
/// reduced-opening Horner arithmetic — ~752 opened columns × 19 FRI queries) is
/// one of the two 2^15-row tables of the measured shrink, and it is
/// packing-reducible WITHOUT moving the global FRI max height (held at 2^15 by
/// the poseidon2-W16 Merkle-hash table, whose height NPO packing is left
/// untouched). Because the FRI shape — query count, fold rounds, blowup — is
/// unchanged, the gnark contract (`chain/gnark/fri_verify_native.go`, compiled
/// at R=18 arity-2 rounds / 19 queries / blowup 64) is unaffected; only this
/// prover's LDE work on the ALU table shrinks.
pub fn default_shrink_packing() -> TablePacking {
    ProveNextLayerParams::default().table_packing
}

/// [`shrink_apex_to_outer`] at a caller-chosen [`TablePacking`]. Use
/// [`default_shrink_packing`] as the baseline; a heavier ALU packing (e.g.
/// `TablePacking::new(1, 8).with_horner_pack_k(4)`) trims the ALU-table LDE.
pub fn shrink_apex_to_outer_with_packing<SC: OuterShrinkConfig>(
    apex: &RecursionOutput<DreggRecursionConfig>,
    inner_config: &DreggRecursionConfig,
    outer_config: &SC,
    packing: &TablePacking,
) -> Result<ApexShrinkProof<SC>, String> {
    let input = apex.into_recursion_input::<BatchOnly>();
    shrink_recursion_input_to_outer_with_packing(&input, inner_config, outer_config, packing)
}

/// The split-config core: build the verifier circuit for `input` under the
/// INNER (BabyBear-hash) config, then commit + prove it under the OUTER
/// (BN254-hash) config. Generic over the recursion input's AIR parameter so a
/// uni-STARK inner proof can flow through the same seam as the batch apex.
///
/// Proves at [`default_shrink_packing`]; use
/// [`shrink_recursion_input_to_outer_with_packing`] to retarget the packing.
pub fn shrink_recursion_input_to_outer<A, SC: OuterShrinkConfig>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
    outer_config: &SC,
) -> Result<ApexShrinkProof<SC>, String>
where
    A: RecursiveAir<P3BabyBear, EF, LogUpGadget>,
{
    shrink_recursion_input_to_outer_with_packing(
        input,
        inner_config,
        outer_config,
        &default_shrink_packing(),
    )
}

/// [`shrink_recursion_input_to_outer`] at an explicit [`TablePacking`]. The
/// SAME `packing` is threaded to both the table-AIR extraction
/// (`get_airs_and_degrees_with_prep`) and the prover (`with_table_packing`), so
/// the shrink proof is internally consistent and self-describing (the verifier
/// rebuilds the AIRs from `proof.table_packing`). The FRI knobs come from
/// `outer_config`, NOT from packing — reducing a non-max table's height never
/// changes the FRI shape the gnark side depends on.
pub fn shrink_recursion_input_to_outer_with_packing<A, SC: OuterShrinkConfig>(
    input: &RecursionInput<'_, DreggRecursionConfig, A>,
    inner_config: &DreggRecursionConfig,
    outer_config: &SC,
    packing: &TablePacking,
) -> Result<ApexShrinkProof<SC>, String>
where
    A: RecursiveAir<P3BabyBear, EF, LogUpGadget>,
{
    let backend = create_recursion_backend();

    // (1) The apex-verifier circuit, built against the INNER config — the
    // in-circuit twin of `verify_all_tables(apex)` at the inner FRI knobs.
    let (circuit, verifier_result) =
        build_next_layer_circuit::<DreggRecursionConfig, A, _, D>(input, inner_config, &backend)
            .map_err(|e| format!("apex-verifier circuit build failed: {e:?}"))?;

    // The constraint profile stays `prove_next_layer`'s default (Standard →
    // Baseline ALU); only the packing is caller-controlled.
    let constraint_profile = ProveNextLayerParams::default().constraint_profile;

    // (2) Extract the circuit's table AIRs + preprocessed columns AT THE OUTER
    // CONFIG. The preprocessor/builder set mirrors the FRI backend's own
    // (`FriRecursionBackendForExt::non_primitive_{preprocessors,air_builders}`
    // at D=4, default knobs: recompose_lanes=1, coeff-lookups OFF because the
    // W16 challenger's extension degree equals D). They are constructed from
    // the fork's public factory functions because the backend's trait methods
    // are typed at the INNER config.
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![
        poseidon2_preprocessor::<P3BabyBear>(),
        recompose_preprocessor::<P3BabyBear>(false),
        expose_claim_preprocessor::<P3BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<SC, D>>> = {
        let mut builders = poseidon2_air_builders::<SC, D>();
        builders.extend(recompose_air_builders::<SC, D>(1, false));
        builders.extend(expose_claim_air_builders::<SC, D>());
        builders
    };
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<SC, EF, D>(
            &circuit,
            packing,
            &preprocessors,
            &air_builders,
            constraint_profile,
        )
        .map_err(|e| format!("outer-config table-AIR extraction failed: {e:?}"))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let ext_degrees: Vec<usize> = degrees.iter().map(|&d| d + outer_config.is_zk()).collect();

    // (3) Witness generation: run the circuit on the apex proof. The FRI
    // private data (the apex's BabyBear Merkle siblings) is injected via the
    // INNER config — it describes the proof being VERIFIED, not the proof
    // being minted.
    let traces = {
        let public_inputs = verifier_result
            .pack_public_inputs(input)
            .map_err(|e| format!("shrink public-input packing failed: {e:?}"))?;
        let private_inputs = verifier_result
            .pack_private_inputs(input)
            .map_err(|e| format!("shrink private-input packing failed: {e:?}"))?;
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&public_inputs)
            .map_err(|e| format!("shrink runner public inputs: {e:?}"))?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|e| format!("shrink runner private inputs: {e:?}"))?;
        // UFCS: `FriVerifierResult` implements `VerifierCircuitResult<SC, A>`
        // for every `A`, and `op_ids` does not mention `A` — pin it.
        let op_ids =
            <_ as VerifierCircuitResult<DreggRecursionConfig, A>>::op_ids(&verifier_result);
        backend
            .set_private_data(inner_config, &mut runner, op_ids, input)
            .map_err(|e| format!("shrink FRI private data: {e}"))?;
        runner
            .run()
            .map_err(|e| format!("apex-verifier witness generation failed: {e:?}"))?
    };

    // (4)+(5) Commit the preprocessed op-list and prove all tables UNDER THE
    // OUTER CONFIG — BN254-native roots, MultiField transcript, the `ir2` FRI
    // shape the gnark verifier was compiled and measured at.
    let prover_data = ProverData::from_airs_and_degrees(outer_config, &airs, &ext_degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    // ALU variant must match what `get_airs_and_degrees_with_prep` built at
    // this constraint profile — the same Standard→Baseline mapping
    // `prove_next_layer` applies.
    let alu_variant = match constraint_profile {
        ConstraintProfile::Standard => AirVariant::Baseline,
        ConstraintProfile::RecursionOptimized => AirVariant::Optimized,
    };
    let prover = outer_shrink_prover(outer_config)
        .with_table_packing(packing.clone())
        .with_alu_variant(alu_variant);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|e| format!("outer-config shrink proving failed: {e}"))?;

    Ok(ApexShrinkProof {
        proof,
        prover_data: Rc::new(circuit_prover_data),
    })
}

/// Verify a BN254-native shrink proof under the outer config — the Rust twin
/// of what the gnark circuit will do natively. Registers the SAME
/// non-primitive table set as
/// [`crate::plonky3_recursion_impl::recursive::verify_recursive_batch_proof`]
/// (the shrink circuit is the same verifier-circuit family, only committed
/// with BN254 hashing).
pub fn verify_shrink_proof<SC: OuterShrinkConfig>(
    proof: &BatchStarkProof<SC>,
    outer_config: &SC,
) -> Result<(), String> {
    outer_shrink_prover(outer_config)
        .verify_all_tables(proof)
        .map_err(|e| format!("shrink proof verification failed: {e:?}"))
}

/// The outer-config batch prover/verifier with the verifier-circuit table set
/// registered: Poseidon2 W16 (the in-circuit FRI challenger), Poseidon2 W24
/// (the isolated IVC segment-digest permutation an apex root carries),
/// recompose (BF→EF packing; no coeff split at D=4), and expose_claim (the
/// host-readable claim channel). Mirrors `prove_next_layer`'s registration via
/// `FriRecursionBackendForExt::non_primitive_provers` — the SAME provers,
/// constructed through `BatchStarkProver`'s public registration API because
/// the backend's are typed at the inner config.
pub(crate) fn outer_shrink_prover<SC: OuterShrinkConfig>(
    outer_config: &SC,
) -> BatchStarkProver<SC> {
    let mut prover = BatchStarkProver::new(outer_config.clone());
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    prover.register_recompose_table::<D>(false);
    prover.register_expose_claim_table::<D>();
    prover
}
