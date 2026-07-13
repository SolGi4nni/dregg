//! GNARK FIXTURE EXPORT for a REAL BN254-native shrink proof — the bridge
//! between [`crate::apex_shrink`] (the Rust side of the wrap) and
//! `chain/gnark/fri_verify_native.go` (the gnark side).
//!
//! [`export_real_shrink_fri_fixture`] takes a real shrink proof (a
//! `BatchStarkProof<DreggOuterConfig>` minted by
//! [`crate::apex_shrink::shrink_apex_to_outer`] over a real `ir2_leaf_wrap`
//! apex) and serializes EVERYTHING the gnark native-hash FRI verifier needs to
//! re-verify the proof's FRI layer against the REAL transcript:
//!
//! 1. **The transcript prefix** — the exact Fiat–Shamir event sequence the
//!    batch-STARK verifier drives BEFORE the FRI commit phase
//!    (`p3_batch_stark::verifier::verify_batch` at the pinned rev `82cfad7`,
//!    mirrored step for step below): instance count, per-instance binding
//!    data, the main/preprocessed/permutation/quotient commitments (native
//!    BN254 digests), public values, LogUp cumulative sums, the sampled
//!    permutation challenges / constraint-folding alpha / zeta, the opened
//!    values (observed inside `TwoAdicFriPcs::verify`), and the FRI
//!    batch-combination alpha. Every sampled value is exported too, so the
//!    gnark circuit can PIN its own transcript against the Rust one
//!    lane-for-lane.
//! 2. **The FRI commit-phase data** — commit roots (one native BN254 element
//!    each), the final polynomial, the query proof-of-work witness, and per
//!    query: the initial reduced opening, the roll-in reduced openings (the
//!    multi-height batch openings folded in as the domain shrinks past each
//!    input height), the per-round sibling evaluations, and the per-round
//!    native Merkle paths.
//! 3. **The INPUT-BATCH openings** (the `open_input` seam, p3-fri
//!    `verifier.rs:524` at the pinned rev) — the structural PCS round shapes
//!    (`input_rounds`: per round, per matrix, the LDE log-height / opened
//!    width / opening-point count / next-point generator bits) and, per query
//!    and per round, the opened rows at the query point plus the native
//!    Merkle path against the round's commitment
//!    (main/quotient/preprocessed/permutation). With these, the gnark side
//!    DERIVES the per-query reduced openings in-circuit — the Merkle
//!    verification of the input batches followed by the alpha-combination
//!    Σ αᵏ·(p(z)−p(x))/(z−x) — and binds them against the FRI fold seeds,
//!    closing the opened-values ↔ commitments soundness seam.
//!
//! ## Why the export is trustworthy (self-checks, run on every export)
//!
//! - The transcript-prefix mirror is validated by handing a challenger
//!   advanced through the RECORDED events to the REAL `TwoAdicFriPcs::verify`
//!   (via the `Pcs` trait) — the real p3 verifier accepting from that
//!   challenger state means the recorded prefix IS the real transcript prefix
//!   (any divergence shifts every beta/query index and fails the FRI check).
//! - The FRI section is validated by re-running the ENTIRE gnark-side flow
//!   host-side with real p3 components: the real `MultiField32Challenger`
//!   (betas, arity schedule, PoW, query indices), the real `ExtensionMmcs`
//!   commit-phase Merkle verification, the real `TwoAdicFriFolding::fold_row`,
//!   an `open_input` replica for the reduced openings, and the final-poly
//!   check. What the fixture contains is exactly what passed this run.
//!
//! ## HONEST SCOPE
//!
//! The fixture drives the gnark side over real data: transcript agreement,
//! commit-phase Merkle openings, fold arithmetic, PoW, final poly, the
//! STARK-algebra layer (constraint eval at zeta + quotient identity), AND —
//! since fixture v2 — the input-batch openings that let the gnark circuit
//! DERIVE the reduced openings from the committed columns (`open_input`).
//! The exported reduced openings (initial + roll-ins) remain in the fixture
//! as the fold-seed witnesses; the gnark circuit re-derives them from the
//! input-batch data and asserts equality, so they are commitment-BOUND, not
//! trusted. Remaining before the Groth16 wrap: bake the shape/DAG as VK
//! constants and size the wrap (see `chain/gnark/stark_verify_native.go`).

use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

use p3_baby_bear::BabyBear;
use p3_batch_stark::ProverData;
use p3_bn254::Bn254;
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_circuit_prover::{
    AirVariant, BatchStarkProof, CircuitProverData, ConstraintProfile, NUM_PRIMITIVE_TABLES,
    common::{NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep},
    expose_claim_air_builders, expose_claim_preprocessor, poseidon2_air_builders,
    poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
};
use p3_commit::{BatchOpening, BatchOpeningRef, Mmcs, Pcs, PolynomialSpace};
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField,
};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Kind, LookupProtocol};
use p3_matrix::Dimensions;
use p3_recursion::{
    BatchOnly, PcsRecursionBackend, ProveNextLayerParams, RecursionOutput, VerifierCircuitResult,
    build_next_layer_circuit_with_expose,
};
use p3_symmetric::{Hash, MerkleCap};
use p3_uni_stark::StarkGenericConfig;
use serde::{Deserialize, Serialize};

use crate::apex_shrink::{ApexShrinkProof, outer_shrink_prover};
use crate::dregg_outer_config::{
    DreggOuterConfig, OUTER_DIGEST_ELEMS, OUTER_FRI_LOG_BLOWUP, OUTER_FRI_NUM_QUERIES,
    OUTER_FRI_QUERY_POW_BITS, OuterChallengeMmcs, OuterChallenger, OuterCompress, OuterHash,
    OuterValMmcs, dregg_poseidon2_bn254,
};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionVk, create_recursion_backend, recursion_vk_fingerprint,
};

const D: usize = 4;
type EF = BinomialExtensionField<BabyBear, D>;
type OuterDigest = [Bn254; OUTER_DIGEST_ELEMS];
type OuterCap = MerkleCap<BabyBear, OuterDigest>;
/// The outer PCS, with its challenger pinned so trait-method calls
/// (`natural_domain_for_degree`, `verify`) are unambiguous.
type OuterPcsT = <DreggOuterConfig as StarkGenericConfig>::Pcs;
type OuterDomain = <OuterPcsT as Pcs<EF, OuterChallenger>>::Domain;
/// One PCS round: a commitment plus, per matrix, (domain, [(point, values)]).
type ComRound = (OuterCap, Vec<(OuterDomain, Vec<(EF, Vec<EF>)>)>);

/// The pinned outer domain for a degree (UFCS: the challenger generic on
/// `Pcs` is otherwise free and inference stalls).
fn outer_domain(pcs: &OuterPcsT, degree: usize) -> OuterDomain {
    <OuterPcsT as Pcs<EF, OuterChallenger>>::natural_domain_for_degree(pcs, degree)
}

// ============================================================================
// THE EXPOSED-CLAIM SHRINK (the settlement-statement binding seam)
// ============================================================================

/// The pinned settlement-statement lane count (genesis_root8 ++ final_root8 ++
/// num_turns ++ chain_digest8) — `chain/gnark`'s `NumPublicInputs`.
pub const SETTLEMENT_CLAIM_LANES: usize = 25;

/// The apex VK-core lane count: the apex's preprocessed commitment is one
/// BabyBear Poseidon2-W16 Merkle root (cap height 0) = 8 BabyBear felts.
/// These ride as lanes `25..33` of the shrink proof's `expose_claim` table
/// (see [`shrink_apex_to_outer_exposed`]).
pub const APEX_VK_LANES: usize = 8;

// ============================================================================
// THE DEPLOYED APEX VK-IDENTITY (RecursionVk → ApexVkLanes)
// ============================================================================

/// The deployed dregg apex's VK identity — the canonical `RecursionVk →
/// ApexVkLanes` derivation record, serialized to
/// `chain/gnark/fixtures/apex_vk_identity.json` for the gnark settlement
/// circuit to bake its apex-VK pin from.
///
/// ## Why the pair is BOUND, not two independent claims
///
/// [`recursion_vk_fingerprint`] (a blake3-32 over the apex's
/// verifier-reconstruction material) hashes the apex's preprocessed
/// commitment `gp.commitment` as a labeled component
/// (`"preprocessed_commitment"`), and `apex_preprocessed_commit` here is the
/// flattened canonical-`u32` felts of the SAME `gp.commitment` object
/// ([`p3_recursion::RecursionOutput::running_preprocessed_commit`] returns
/// exactly the value the fingerprint serializes). By blake3 collision
/// resistance, VK material that fingerprints to a given `recursion_vk_hex`
/// cannot carry different lanes.
///
/// And the anchor is CHECKED, not merely carried: the derived fingerprint is
/// asserted `==` the governance-pinned [`DREGG_APEX_RECURSION_VK`] constant
/// (the weak-subjectivity anchor) by [`check_apex_vk_identity_pin`] — in the
/// derivation lane before the artifact is emitted, and again by every
/// consumer at load (`chain/gnark` `loadApexVkIdentity` over the same
/// constant, `DreggApexRecursionVk`). The lanes are bound to that pinned
/// fingerprint by the self-binding pair above, so a doctored identity —
/// different fingerprint, or lanes the pinned fingerprint does not hash —
/// REJECTS instead of being trusted because it sits at HEAD.
///
/// VK material is content-independent (two proofs of the same circuit over
/// different data carry identical material) and — with the accumulator's WRAP
/// step ON — depth-invariant, so a fresh fold of ANY chain at HEAD derives
/// the deployed circuit's identity. `derive_deployed_apex_vk_identity_and_check_fixture`
/// (tests/apex_shrink_gnark_fixture.rs) is the minting + differential gate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApexVkIdentity {
    /// Artifact schema version.
    pub version: u32,
    /// Hex of the apex's [`RecursionVk`] fingerprint
    /// ([`recursion_vk_fingerprint`]) — asserted equal to the
    /// governance-pinned [`DREGG_APEX_RECURSION_VK`] anchor at load
    /// ([`check_apex_vk_identity_pin`]; `chain/gnark` mirrors the check over
    /// `DreggApexRecursionVk`).
    pub recursion_vk_hex: String,
    /// The apex's preprocessed commitment (its VK-identity core) as
    /// [`APEX_VK_LANES`] canonical BabyBear `u32` lanes — the value
    /// `chain/gnark`'s `SettlementCircuit` bakes as `apexPreprocessedCommit`.
    pub apex_preprocessed_commit: Vec<u32>,
    /// Human-readable provenance note (how to regenerate/re-check).
    pub description: String,
}

/// The GOVERNANCE-PINNED deployed-apex [`RecursionVk`] fingerprint (blake3-32,
/// hex) — dregg's apex weak-subjectivity anchor, the exact analogue of the
/// Solana bridge's pinned `WeakSubjectivityAnchor`
/// (`bridge/src/solana_trustless.rs` `check_pinned_anchor`): a value
/// governance commits to at deploy time, which every consumer of the derived
/// identity artifact asserts against, fail-closed.
///
/// Enforced by [`check_apex_vk_identity_pin`] here and by `chain/gnark`'s
/// `loadApexVkIdentity` over the mirrored Go constant `DreggApexRecursionVk`
/// (`settlement_circuit.go`): an `apex_vk_identity.json` whose
/// `recursion_vk_hex` differs REJECTS at load. The `ApexVkLanes` are bound to
/// this fingerprint by the [`recursion_vk_fingerprint`] self-binding pair
/// (the fingerprint hashes `gp.commitment`, whose roots ARE the lanes),
/// enforced where the VK material exists: the derivation lane
/// (`derive_deployed_apex_vk_identity_and_check_fixture`) computes fingerprint
/// and lanes from the SAME object and asserts the fingerprint equals THIS pin
/// before emitting the artifact.
///
/// HONEST RESIDUAL (same shape as the Solana anchor pin): the constant is
/// committed in-repo — governance chooses it at deploy, and an apex circuit
/// change requires a governance step to re-derive and update it (here AND the
/// Go mirror); until then, identity loads fail closed. The trust model is
/// weak subjectivity — "trust a governance-pinned recent fingerprint" — not
/// "trust whoever compiled the artifact at HEAD".
pub const DREGG_APEX_RECURSION_VK: &str =
    "3ad1c9c601686a0983ed8df43a4a145e729d985194386ec22156029b92fc5503";

/// Assert an [`ApexVkIdentity`]'s fingerprint equals the governance-pinned
/// [`DREGG_APEX_RECURSION_VK`] anchor — fail-closed. This is the check that
/// makes the anchor authoritative rather than decorative: without it the
/// artifact's `recursion_vk_hex` was validated only as 32-byte hex and used
/// in error messages.
pub fn check_apex_vk_identity_pin(id: &ApexVkIdentity) -> Result<(), String> {
    if id.recursion_vk_hex == DREGG_APEX_RECURSION_VK {
        Ok(())
    } else {
        Err(format!(
            "apex VK identity fingerprint {} != governance-pinned DREGG_APEX_RECURSION_VK {} — \
             either the identity artifact is doctored/stale, or the apex circuit changed and \
             governance has not re-pinned the anchor (re-derive via \
             derive_deployed_apex_vk_identity_and_check_fixture, then update the constant here \
             AND chain/gnark/settlement_circuit.go DreggApexRecursionVk)",
            id.recursion_vk_hex, DREGG_APEX_RECURSION_VK,
        ))
    }
}

/// Derive the apex's VK identity — its [`RecursionVk`] fingerprint together
/// with the [`APEX_VK_LANES`] preprocessed-commitment lanes that fingerprint
/// hashes — from an apex proof's verifier-reconstruction material.
///
/// The proof argument is a CARRIER of the circuit's VK material, not a trust
/// root: the material is content-independent, and the returned pair is
/// self-binding (see [`ApexVkIdentity`]) — [`check_apex_vk_identity_pin`]
/// asserts `recursion_vk_hex` against the governance-pinned
/// [`DREGG_APEX_RECURSION_VK`] anchor, and then the lanes are the deployed
/// apex's.
pub fn derive_apex_vk_identity(
    apex: &RecursionOutput<DreggRecursionConfig>,
) -> Result<ApexVkIdentity, String> {
    let commit = apex
        .running_preprocessed_commit()
        .ok_or("apex proof carries no preprocessed commitment (no VK core)")?;
    let lanes: Vec<u32> = commit
        .roots()
        .iter()
        .flat_map(|r| r.iter().map(|v| v.as_canonical_u32()))
        .collect();
    if lanes.len() != APEX_VK_LANES {
        return Err(format!(
            "apex preprocessed commitment has {} felts, the pinned VK-core shape is {APEX_VK_LANES} \
             (cap height drifted — refusing to derive an unexpected shape)",
            lanes.len(),
        ));
    }
    let vk: RecursionVk = recursion_vk_fingerprint(&apex.0);
    Ok(ApexVkIdentity {
        version: 1,
        recursion_vk_hex: vk.to_hex(),
        apex_preprocessed_commit: lanes,
        description: "The deployed dregg apex's VK identity: recursion_vk_hex is the blake3-32 \
                      RecursionVk fingerprint, asserted at load against the governance-pinned \
                      DREGG_APEX_RECURSION_VK / DreggApexRecursionVk constant (the \
                      weak-subjectivity anchor); apex_preprocessed_commit is the flattened \
                      preprocessed commitment the fingerprint hashes (the ApexVkLanes value the \
                      gnark SettlementCircuit bakes as its apex-VK pin). Regenerate + \
                      differential-check against the proof fixture: cargo test -p \
                      dregg-circuit-prove --release --test apex_shrink_gnark_fixture \
                      derive_deployed -- --ignored --nocapture"
            .to_string(),
    })
}

/// Shrink a REAL apex into a BN254-native-hash proof **with the apex's exposed
/// 25-lane chain claim RE-EXPOSED through the shrink proof's OWN
/// `expose_claim` table** — the seam that makes the settlement statement
/// externally bound.
///
/// ## Why [`crate::apex_shrink::shrink_apex_to_outer`] is NOT enough for settlement
///
/// The plain shrink verifies the apex in-circuit, and the apex's 25-lane claim
/// (`[genesis_root8, final_root8, num_turns, chain_digest8]`, the apex's
/// `expose_claim` public values) enters the shrink circuit as PUBLIC INPUTS —
/// which land in the shrink proof's **Public table trace**. That trace is
/// committed and opened only at zeta (plus random FRI query points), so an
/// EXTERNAL verifier (the gnark wrap) has **no sound way to read the claim
/// back out**: binding witnessed rows to the single opened evaluation at zeta
/// is forgeable (any vector agreeing with the real one at zeta passes — the
/// prover knows zeta when it picks the witness, so Schwartz–Zippel gives
/// nothing; the kernel of "evaluate at zeta" has dimension ≥ height − 4 per
/// column).
///
/// ## What this entrypoint changes
///
/// The apex-verifier circuit is built with
/// [`build_next_layer_circuit_with_expose`]: after the verifier constraints
/// are emitted, the hook re-exposes the apex `expose_claim` instance's
/// public-input targets through the SHRINK circuit's own `expose_claim`
/// table. The shrink proof then carries the 25 claim lanes as
/// `non_primitives[expose_claim].public_values`, where they are
///
///   1. observed into the shrink proof's Fiat–Shamir transcript (verify_batch
///      observes per-instance public values right after the main commitment),
///      and
///   2. constrained by the `ExposeClaimAir` AIR — `public_value[lane] == v_0`
///      of the cell read off the `WitnessChecks` bus, which is bus-bound to
///      the SAME circuit witnesses the in-circuit apex verification consumed
///      as the apex's public values — via the quotient identity at zeta, i.e.
///      by the full vanishing argument, not a prover-chosen evaluation.
///
/// So "this shrink proof verifies with public values X" now MEANS "the
/// verified apex exposes claim X". The gnark wrap equates X with its 25
/// Groth16 public inputs (see `chain/gnark/settlement_circuit.go`).
///
/// ## THE APEX-VK PIN (which apex? — closing the same-shape-forgery seam)
///
/// The apex's preprocessed commitment (its VK-identity core — the exact value
/// [`recursion_vk_fingerprint`](crate::plonky3_recursion_impl::recursive::recursion_vk_fingerprint)
/// hashes and the BabyBear IVC pins at every fold) enters the verifier circuit
/// as PROVER-SUPPLIED public inputs, otherwise verified only against itself: a
/// same-shape malicious apex with doctored preprocessed columns could steer
/// its expose_claim to ANY (genesis, final) pair and still shrink+settle. Two
/// welds close it here:
///
/// 1. **In-circuit pin (lever (a)).** The apex is folded via
///    [`RecursionOutput::into_recursion_input_pinned`]: the fork's
///    `pin_preprocessed_commit` bakes the apex's preprocessed commitment as
///    circuit CONSTANTS and `connect`s them to the very public-input targets
///    the in-circuit apex verification consumes — a different-preprocessed
///    apex makes THIS shrink circuit UNSAT (and a different circuit changes
///    the shrink's own preprocessed root, which the gnark side already pins).
/// 2. **Exposure ([`APEX_VK_LANES`] lanes).** The SAME constants are
///    re-exposed through the shrink's `expose_claim` table, after the 25-lane
///    chain claim (lanes `25..33`), so the gnark settlement circuit can
///    assert them equal to the DEPLOYED dregg apex's commitment as a baked
///    Groth16-VK constant (`chain/gnark/settlement_circuit.go`
///    `apexPreprocessedCommit`). Constant-cell values are enforced by the
///    Const table's preprocessed columns, so the exposed lanes are
///    bus-bound to the same cells the pin constrained — the lanes ARE the
///    apex VK the in-circuit verification ran against.
///
/// Same split-config five steps as
/// [`crate::apex_shrink::shrink_recursion_input_to_outer_with_packing`], at
/// [`crate::apex_shrink::default_shrink_packing`].
pub fn shrink_apex_to_outer_exposed(
    apex: &RecursionOutput<DreggRecursionConfig>,
    inner_config: &DreggRecursionConfig,
    outer_config: &DreggOuterConfig,
) -> Result<ApexShrinkProof, String> {
    // Pin to the apex's own preprocessed commitment (the fixture-mint path:
    // the apex IS the deployed dregg apex, so its commitment IS the deployed
    // value — the derivation test `derive_deployed_apex_vk_identity_and_check_fixture`
    // re-derives that value from a FRESH fold at HEAD via
    // [`derive_apex_vk_identity`] and asserts the fixture matches). A
    // settlement SERVICE receiving untrusted apexes should call
    // [`shrink_apex_to_outer_exposed_pinned_to`] with the deployed constant
    // (an anchor-checked [`ApexVkIdentity`]) instead.
    let apex_pre_commit = apex
        .running_preprocessed_commit()
        .ok_or("apex proof carries no preprocessed commitment (no VK core to pin)")?;
    shrink_apex_to_outer_exposed_pinned_to(apex, inner_config, outer_config, apex_pre_commit)
}

/// The runtime preprocessed-commitment value type of the inner (apex) config —
/// the apex's VK-identity core (a Merkle cap of one Poseidon2-W16 root).
pub type ApexVkCommit = <<DreggRecursionConfig as StarkGenericConfig>::Pcs as Pcs<
    <DreggRecursionConfig as StarkGenericConfig>::Challenge,
    <DreggRecursionConfig as StarkGenericConfig>::Challenger,
>>::Commitment;

/// [`shrink_apex_to_outer_exposed`] with the apex-VK pin supplied by the
/// CALLER: the shrink circuit is pinned to `expected_apex_pre_commit` (baked
/// constants `connect`ed to the apex-verification's preprocessed-commitment
/// inputs, and re-exposed as claim lanes 25..33). An apex whose preprocessed
/// commitment differs — a same-shape malicious apex — fails witness
/// generation/proving (the pin canary in `tests/apex_shrink_gnark_fixture.rs`
/// exercises exactly this).
pub fn shrink_apex_to_outer_exposed_pinned_to(
    apex: &RecursionOutput<DreggRecursionConfig>,
    inner_config: &DreggRecursionConfig,
    outer_config: &DreggOuterConfig,
    apex_pre_commit: ApexVkCommit,
) -> Result<ApexShrinkProof, String> {
    // Locate the apex's expose_claim instance (its 25-lane claim channel).
    let claim_pos = apex
        .0
        .non_primitives
        .iter()
        .position(|e| e.op_type.as_str() == "expose_claim")
        .ok_or("apex proof carries no expose_claim table (no claim to re-expose)")?;
    let claim_idx = NUM_PRIMITIVE_TABLES + claim_pos;
    let claim_len = apex.0.non_primitives[claim_pos].public_values.len();
    if claim_len == 0 {
        return Err("apex expose_claim table carries no public values".into());
    }
    let apex_vk_felts: Vec<BabyBear> = apex_pre_commit
        .roots()
        .iter()
        .flat_map(|r| r.iter().copied())
        .collect();
    if apex_vk_felts.len() != APEX_VK_LANES {
        return Err(format!(
            "apex preprocessed commitment has {} felts, the pinned VK-core shape is {} \
             (cap height drifted — refusing to expose an unexpected shape)",
            apex_vk_felts.len(),
            APEX_VK_LANES
        ));
    }
    let apex_vk_vals: Vec<EF> = apex_vk_felts.iter().map(|&f| EF::from(f)).collect();

    // Lever (a): fold the apex PINNED — the verifier circuit constrains the
    // apex's preprocessed-commitment public inputs to equal baked constants.
    let input = apex.into_recursion_input_pinned::<BatchOnly>(apex_pre_commit.clone());
    let backend = create_recursion_backend();

    // (1) The apex-verifier circuit + the claim & apex-VK re-exposure hook.
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<EF>,
                       apt: &[Vec<p3_recursion::Target>]| {
        let claim = &apt[claim_idx];
        assert_eq!(
            claim.len(),
            claim_len,
            "apex claim target count drifted from the proof's public values"
        );
        // ONE expose_claim table: the 25 chain-claim lanes, then the 8
        // apex-VK-core lanes. `alloc_const` memoizes by value, so these are
        // the SAME const cells `pin_preprocessed_commit` connected to the
        // apex-verification's preprocessed-commitment inputs.
        let mut lanes = claim.clone();
        for &v in &apex_vk_vals {
            lanes.push(cb.alloc_const(
                v,
                "apex VK-core lane (deployed-apex preprocessed commitment)",
            ));
        }
        cb.expose_as_public_output(&lanes);
    };
    let (circuit, verifier_result) = build_next_layer_circuit_with_expose::<
        DreggRecursionConfig,
        BatchOnly,
        _,
        D,
    >(&input, inner_config, &backend, Some(&expose))
    .map_err(|e| format!("apex-verifier circuit build (with exposed claim) failed: {e:?}"))?;

    // Steps (2)-(5): identical to the plain shrink (apex_shrink.rs), at the
    // default packing + Standard constraint profile.
    let packing = crate::apex_shrink::default_shrink_packing();
    let constraint_profile = ProveNextLayerParams::default().constraint_profile;

    let preprocessors: Vec<Box<dyn NpoPreprocessor<BabyBear>>> = vec![
        poseidon2_preprocessor::<BabyBear>(),
        recompose_preprocessor::<BabyBear>(false),
        expose_claim_preprocessor::<BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggOuterConfig, D>>> = {
        let mut builders = poseidon2_air_builders::<DreggOuterConfig, D>();
        builders.extend(recompose_air_builders::<DreggOuterConfig, D>(1, false));
        builders.extend(expose_claim_air_builders::<DreggOuterConfig, D>());
        builders
    };
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<DreggOuterConfig, EF, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            constraint_profile,
        )
        .map_err(|e| format!("outer-config table-AIR extraction failed: {e:?}"))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let ext_degrees: Vec<usize> = degrees.iter().map(|&d| d + outer_config.is_zk()).collect();

    // (3) Witness generation over the real apex.
    let traces = {
        let public_inputs = verifier_result
            .pack_public_inputs(&input)
            .map_err(|e| format!("shrink public-input packing failed: {e:?}"))?;
        let private_inputs = verifier_result
            .pack_private_inputs(&input)
            .map_err(|e| format!("shrink private-input packing failed: {e:?}"))?;
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&public_inputs)
            .map_err(|e| format!("shrink runner public inputs: {e:?}"))?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|e| format!("shrink runner private inputs: {e:?}"))?;
        let op_ids =
            <_ as VerifierCircuitResult<DreggRecursionConfig, BatchOnly>>::op_ids(&verifier_result);
        backend
            .set_private_data(inner_config, &mut runner, op_ids, &input)
            .map_err(|e| format!("shrink FRI private data: {e}"))?;
        runner
            .run()
            .map_err(|e| format!("apex-verifier witness generation failed: {e:?}"))?
    };

    // (4)+(5) Commit + prove under the outer config.
    let prover_data = ProverData::from_airs_and_degrees(outer_config, &airs, &ext_degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    let alu_variant = match constraint_profile {
        ConstraintProfile::Standard => AirVariant::Baseline,
        ConstraintProfile::RecursionOptimized => AirVariant::Optimized,
    };
    let prover = outer_shrink_prover(outer_config)
        .with_table_packing(packing.clone())
        .with_alu_variant(alu_variant);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|e| format!("outer-config exposed-shrink proving failed: {e}"))?;

    // Self-check: the shrink proof's OWN expose_claim public values equal the
    // apex's claim FOLLOWED BY the apex's preprocessed commitment (the VK-core
    // lanes), lane for lane (the re-exposure is faithful).
    let shrunk_claim = proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .ok_or("exposed shrink proof carries no expose_claim table")?;
    let mut expected_lanes = apex.0.non_primitives[claim_pos].public_values.clone();
    expected_lanes.extend(apex_vk_felts.iter().copied());
    if shrunk_claim.public_values != expected_lanes {
        return Err(format!(
            "re-exposed lanes {:?} != apex claim ++ apex VK-core {:?}",
            shrunk_claim.public_values, expected_lanes
        ));
    }

    Ok(ApexShrinkProof {
        proof,
        prover_data: Rc::new(circuit_prover_data),
    })
}

// ============================================================================
// Fixture schema (mirrored by chain/gnark/apex_shrink_real_fixture_test.go)
// ============================================================================

/// One transcript event of the pre-FRI prefix, replayed by the gnark circuit
/// through its `MultiFieldChallenger` gadget.
///
/// Event boundaries matter ONLY for digests (each `observe_digest` is one
/// native absorb call with its own length tag); BabyBear observes/samples are
/// per-value and may be coalesced freely.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FixtureEvent {
    /// Observe canonical BabyBear proof values, in order.
    ObserveBb { values: Vec<u32> },
    /// Observe ONE native BN254 digest (one `ObserveBn254Digest` call).
    ObserveDigest { words: Vec<String> },
    /// Sample BabyBear challenges; `values` are the expected canonical
    /// results, asserted in-circuit (transcript pinning).
    SampleBb { values: Vec<u32> },
}

/// FRI shape parameters (must match `create_outer_config`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FixtureFriShape {
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub commit_pow_bits: usize,
    pub query_pow_bits: usize,
    pub extra_query_index_bits: usize,
    /// Number of commit-phase rounds (all arity 2).
    pub rounds: usize,
    /// `rounds + log_blowup + log_final_poly_len`.
    pub log_global_max_height: usize,
}

/// One input-batch matrix's structural shape (VK-side data; the widths and
/// degree bits are also transcript-bound by the binding block). The order of
/// matrices per round is EXACTLY `verify_batch`'s `coms_to_verify` order —
/// the same order the opened-values-at-zeta stream flattens in, so the gnark
/// side consumes that stream sequentially during the alpha-combination.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixtureInputMatrix {
    /// log2 of the COMMITTED (LDE) height: `log2(domain.size()) + log_blowup`.
    pub log_height: usize,
    /// Opened row width (base-field columns).
    pub width: usize,
    /// Opening points: 1 = zeta only; 2 = zeta then zeta_next.
    pub num_points: usize,
    /// When `num_points == 2`: log2 of the TRACE domain whose subgroup
    /// generator advances zeta to zeta_next (`domain.next_point`,
    /// commit/src/domain.rs:169: multiplication by the subgroup generator).
    /// 0 when `num_points == 1`.
    pub next_point_bits: usize,
}

/// One PCS input round's structural shape (matrices in batch order).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FixtureInputRound {
    pub matrices: Vec<FixtureInputMatrix>,
}

/// One query's opening of ONE input batch (aligned with `input_rounds`):
/// the opened rows at the query point (one per matrix, batch order) and the
/// native Merkle path (bottom-up, one BN254 word per level of the batch
/// tree — `max(log_height)` levels; lower matrices inject via row hashes,
/// not path nodes — merkle-tree/src/mmcs.rs:1052 `verify_batch`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FixtureInputBatch {
    pub rows: Vec<Vec<u32>>,
    pub path: Vec<String>,
}

/// One query's FRI opening data.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FixtureQuery {
    /// The expected sampled query index (pinned in-circuit).
    pub expected_index: u64,
    /// Reduced opening at `log_global_max_height` (the fold seed). Since
    /// fixture v2 the gnark circuit RE-DERIVES this from `input_openings`
    /// and asserts equality (commitment binding).
    pub initial_eval: [u32; 4],
    /// Reduced openings rolled in as the fold passes each input height,
    /// aligned with `roll_in_rounds` (same order). Re-derived in-circuit
    /// like `initial_eval`.
    pub roll_ins: Vec<[u32; 4]>,
    /// Per commit round: the sibling evaluation (arity 2 ⇒ one per round).
    pub siblings: Vec<[u32; 4]>,
    /// Per commit round: the native Merkle path (bottom-up, one BN254 word
    /// per level; round r has `log_global_max_height - r - 1` levels).
    pub merkle_paths: Vec<Vec<String>>,
    /// Per input round (aligned with `input_rounds`): the opened rows at the
    /// query point + the batch Merkle path (the `open_input` witnesses).
    pub input_openings: Vec<FixtureInputBatch>,
}

/// The full gnark fixture for one real shrink proof.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RealShrinkFriFixture {
    pub version: u32,
    pub description: String,
    /// Per-instance `log2(extended trace domain)` of the shrink proof.
    pub degree_bits: Vec<usize>,
    /// Per-instance table PUBLIC VALUES (canonical BabyBear lanes), in
    /// instance order — primitive tables carry none; the `expose_claim`
    /// instance carries the re-exposed 25-lane chain claim FOLLOWED BY the
    /// 8 apex VK-core lanes (the apex's preprocessed commitment — see
    /// [`shrink_apex_to_outer_exposed`], THE APEX-VK PIN). These are the
    /// exact values `verify_batch` observes into the transcript right after
    /// the main commitment, and the `ExposeClaimAir` constraints bind them to
    /// the committed trace.
    pub table_publics: Vec<Vec<u32>>,
    /// Instance index of the shrink proof's own `expose_claim` table (the
    /// settlement claim channel).
    pub claim_instance: usize,
    /// The apex's preprocessed commitment (the deployed dregg apex's
    /// VK-identity core, 8 canonical BabyBear lanes) — a labeled copy of
    /// `table_publics[claim_instance][25..33]`, the value
    /// `chain/gnark/settlement_circuit.go` bakes as `apexPreprocessedCommit`.
    /// Fail-closed cross-checked against the claim-channel tail by the gnark
    /// loader.
    pub apex_preprocessed_commit: Vec<u32>,
    pub fri: FixtureFriShape,
    /// The pre-FRI transcript, `initialise_challenger()` through the FRI
    /// batch-combination alpha sample (inclusive).
    pub prefix_events: Vec<FixtureEvent>,
    /// Commit-phase Merkle roots (native BN254), in round order.
    pub commit_roots: Vec<String>,
    /// Expected betas (pinned in-circuit after each root observe).
    pub expected_betas: Vec<[u32; 4]>,
    /// Final polynomial coefficients (length `2^log_final_poly_len`).
    pub final_poly: Vec<[u32; 4]>,
    /// The query proof-of-work witness.
    pub query_pow_witness: u32,
    /// Rounds AFTER whose fold a reduced opening rolls in (ascending;
    /// identical across queries — the input heights are structural).
    pub roll_in_rounds: Vec<usize>,
    /// The structural PCS input-round shapes (trace, quotient, preprocessed,
    /// permutation — `verify_batch`'s `coms_to_verify` order).
    pub input_rounds: Vec<FixtureInputRound>,
    pub queries: Vec<FixtureQuery>,
}

// ============================================================================
// Recording challenger
// ============================================================================

fn bb_u32(v: &BabyBear) -> u32 {
    v.as_canonical_u32()
}

fn bn254_hex(v: &Bn254) -> String {
    format!("0x{:064x}", v.as_canonical_biguint())
}

fn ef_coords(e: &EF) -> [u32; 4] {
    let s = e.as_basis_coefficients_slice();
    [bb_u32(&s[0]), bb_u32(&s[1]), bb_u32(&s[2]), bb_u32(&s[3])]
}

/// Drives a REAL `MultiField32Challenger` while recording every event, so the
/// gnark side can replay the identical transcript.
struct Recorder {
    ch: OuterChallenger,
    events: Vec<FixtureEvent>,
}

impl Recorder {
    fn new(ch: OuterChallenger) -> Self {
        Self {
            ch,
            events: Vec::new(),
        }
    }

    fn obs_bb(&mut self, v: BabyBear) {
        self.ch.observe(v);
        if let Some(FixtureEvent::ObserveBb { values }) = self.events.last_mut() {
            values.push(bb_u32(&v));
        } else {
            self.events.push(FixtureEvent::ObserveBb {
                values: vec![bb_u32(&v)],
            });
        }
    }

    fn obs_bb_slice(&mut self, vs: &[BabyBear]) {
        for v in vs {
            self.obs_bb(*v);
        }
    }

    /// `observe_algebra_element`: the extension element's base coefficients.
    fn obs_ext(&mut self, e: &EF) {
        self.obs_bb_slice(e.as_basis_coefficients_slice());
    }

    /// `BatchTranscript::observe_usize`: the value lifted to the challenge
    /// field (coefficients `[v, 0, 0, 0]`).
    fn obs_usize(&mut self, v: usize) {
        self.obs_ext(&EF::from(BabyBear::from_usize(v)));
    }

    /// Observe a Merkle cap exactly as `MultiField32Challenger` does: one
    /// native digest absorb per cap root. NEVER coalesced (each call has its
    /// own length tag).
    fn obs_cap(&mut self, cap: &OuterCap) {
        for root in cap.roots() {
            self.ch
                .observe(Hash::<BabyBear, Bn254, OUTER_DIGEST_ELEMS>::from(*root));
            self.events.push(FixtureEvent::ObserveDigest {
                words: root.iter().map(bn254_hex).collect(),
            });
        }
    }

    /// `sample_algebra_element::<EF>`: four base samples, recorded as
    /// expected values.
    fn sample_ext(&mut self) -> EF {
        let e: EF = self.ch.sample_algebra_element();
        let c = ef_coords(&e);
        if let Some(FixtureEvent::SampleBb { values }) = self.events.last_mut() {
            values.extend_from_slice(&c);
        } else {
            self.events
                .push(FixtureEvent::SampleBb { values: c.to_vec() });
        }
        e
    }
}

// ============================================================================
// The export
// ============================================================================

fn reverse_bits_len(x: usize, bits: usize) -> usize {
    let mut out = 0usize;
    for i in 0..bits {
        out |= ((x >> i) & 1) << (bits - 1 - i);
    }
    out
}

fn log2_strict(n: usize) -> usize {
    debug_assert!(n.is_power_of_two());
    n.trailing_zeros() as usize
}

/// The verifier-side `open_input` (p3-fri `verifier.rs:524` at rev `82cfad7`),
/// replicated so the per-query reduced openings can be EXPORTED (the real
/// function is private and returns them only transiently). Includes the real
/// input-MMCS batch verification, so a mis-built round structure fails here,
/// not in gnark.
#[allow(clippy::type_complexity)]
fn open_input_replica(
    log_blowup: usize,
    log_global_max_height: usize,
    index: usize,
    input_proof: &[BatchOpening<BabyBear, OuterValMmcs>],
    alpha: EF,
    val_mmcs: &OuterValMmcs,
    coms: &[ComRound],
) -> Result<Vec<(usize, EF)>, String> {
    if input_proof.len() != coms.len() {
        return Err(format!(
            "input proof has {} batches, expected {}",
            input_proof.len(),
            coms.len()
        ));
    }
    // log_height -> (alpha_pow, reduced_opening)
    let mut reduced = BTreeMap::<usize, (EF, EF)>::new();

    for (batch_opening, (batch_commit, mats)) in input_proof.iter().zip(coms.iter()) {
        let batch_heights: Vec<usize> = mats
            .iter()
            .map(|(domain, _)| domain.size() << log_blowup)
            .collect();
        let batch_dims: Vec<Dimensions> = batch_heights
            .iter()
            .map(|&height| Dimensions { width: 0, height })
            .collect();
        let reduced_index = batch_heights
            .iter()
            .max()
            .map(|&h| index >> (log_global_max_height - log2_strict(h)))
            .unwrap_or(0);
        val_mmcs
            .verify_batch(
                batch_commit,
                &batch_dims,
                reduced_index,
                BatchOpeningRef::new(&batch_opening.opened_values, &batch_opening.opening_proof),
            )
            .map_err(|e| format!("input batch opening failed host-side verification: {e:?}"))?;

        for (mat_opening, (mat_domain, mat_points_and_values)) in
            batch_opening.opened_values.iter().zip(mats.iter())
        {
            let log_height = log2_strict(mat_domain.size()) + log_blowup;
            let bits_reduced = log_global_max_height - log_height;
            let rev_reduced_index = reverse_bits_len(index >> bits_reduced, log_height);
            let x = BabyBear::GENERATOR
                * BabyBear::two_adic_generator(log_height).exp_u64(rev_reduced_index as u64);

            let (alpha_pow, ro) = reduced.entry(log_height).or_insert((EF::ONE, EF::ZERO));
            for (z, ps_at_z) in mat_points_and_values {
                let quotient = (*z - EF::from(x)).inverse();
                if mat_opening.len() != ps_at_z.len() {
                    return Err("opened-width mismatch between input proof and round".into());
                }
                for (&p_at_x, &p_at_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    *ro += *alpha_pow * (p_at_z - EF::from(p_at_x)) * quotient;
                    *alpha_pow *= alpha;
                }
            }
        }
    }

    Ok(reduced
        .into_iter()
        .rev()
        .map(|(lh, (_, ro))| (lh, ro))
        .collect())
}

/// Export the gnark FRI fixture from a REAL shrink proof, self-checking every
/// section against the real p3 verifier components (see the module doc).
pub fn export_real_shrink_fri_fixture(
    proof: &BatchStarkProof<DreggOuterConfig>,
    config: &DreggOuterConfig,
) -> Result<RealShrinkFriFixture, String> {
    if config.is_zk() != 0 {
        return Err("exporter assumes a non-ZK outer config".into());
    }
    if proof.ext_degree != D {
        return Err(format!("expected ext_degree {D}, got {}", proof.ext_degree));
    }
    let p = &proof.proof;
    let n = p.degree_bits.len();
    if p.commitments.random.is_some() {
        return Err("unexpected ZK randomization commitment".into());
    }
    if p.opened_values.instances.len() != n {
        return Err("instance count mismatch between opened values and degree_bits".into());
    }
    if NUM_PRIMITIVE_TABLES + proof.non_primitives.len() != n {
        return Err(format!(
            "instance count {} != {} primitive + {} non-primitive tables",
            n,
            NUM_PRIMITIVE_TABLES,
            proof.non_primitives.len()
        ));
    }

    // Public values in instance order: primitive tables have none, dynamic
    // tables carry theirs in the proof (rebuild_airs_pvs_common's order).
    let mut publics: Vec<Vec<BabyBear>> = vec![Vec::new(); NUM_PRIMITIVE_TABLES];
    publics.extend(proof.non_primitives.iter().map(|e| e.public_values.clone()));

    // The settlement claim channel: the shrink proof's OWN expose_claim table
    // (fixture v3 REQUIRES it — a claimless shrink cannot bind a settlement
    // statement; mint via `shrink_apex_to_outer_exposed`).
    let claim_instance = NUM_PRIMITIVE_TABLES
        + proof
            .non_primitives
            .iter()
            .position(|e| e.op_type.as_str() == "expose_claim")
            .ok_or(
                "shrink proof carries no expose_claim table — the settlement claim is unbound \
                 (mint with shrink_apex_to_outer_exposed, not the plain shrink)",
            )?;
    if publics[claim_instance].len() != SETTLEMENT_CLAIM_LANES + APEX_VK_LANES {
        return Err(format!(
            "shrink expose_claim table carries {} lanes, want {} claim + {} apex-VK \
             (mint with shrink_apex_to_outer_exposed, which pins+exposes the apex VK core)",
            publics[claim_instance].len(),
            SETTLEMENT_CLAIM_LANES,
            APEX_VK_LANES
        ));
    }
    let apex_preprocessed_commit: Vec<u32> = publics[claim_instance][SETTLEMENT_CLAIM_LANES..]
        .iter()
        .map(bb_u32)
        .collect();

    // Lookup contexts + preprocessed binding, rebuilt exactly as the verifier
    // rebuilds them (public fork API).
    let common = outer_shrink_prover(config)
        .rebuild_verifiable_common::<D>(proof, proof.w_binomial)
        .map_err(|e| format!("rebuild_verifiable_common failed: {e:?}"))?;

    // ---- Phase A: the pre-FRI transcript, mirrored + recorded --------------
    // Mirror of p3_batch_stark::verifier::verify_batch (rev 82cfad7) up to and
    // including the pcs.verify opened-value observes and the FRI alpha sample.
    let mut rec = Recorder::new(config.initialise_challenger());

    // observe_instance_count
    rec.obs_usize(n);
    // per-instance observe_instance_binding(ext_db, base_db, width, n_chunks)
    for i in 0..n {
        let inst = &p.opened_values.instances[i].base_opened_values;
        let ext_db = p.degree_bits[i];
        rec.obs_usize(ext_db);
        rec.obs_usize(ext_db); // base_db == ext_db (is_zk = 0)
        rec.obs_usize(inst.trace_local.len());
        rec.obs_usize(inst.quotient_chunks.len());
    }
    // observe_main: main commitment, then per-instance public values.
    rec.obs_cap(&p.commitments.main);
    for pv in &publics {
        rec.obs_bb_slice(pv);
    }
    // observe_preprocessed: widths (all instances), then the global commitment.
    let preprocessed_widths: Vec<usize> = (0..n)
        .map(|i| {
            common
                .preprocessed
                .as_ref()
                .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
                .unwrap_or(0)
        })
        .collect();
    for &w in &preprocessed_widths {
        rec.obs_usize(w);
    }
    if let Some(global) = &common.preprocessed {
        rec.obs_cap(&global.commitment);
    }
    // sample_perm_challenges: global buses share, locals are fresh.
    let lookup_gadget = LogUpGadget::new();
    let n_ch = lookup_gadget.num_challenges();
    let mut seen_buses: HashMap<String, ()> = HashMap::new();
    for lookups in &common.lookups {
        for ctx in lookups.as_ref() {
            match &ctx.kind {
                Kind::Global(name) => {
                    if seen_buses.insert(name.clone(), ()).is_none() {
                        for _ in 0..n_ch {
                            let _ = rec.sample_ext();
                        }
                    }
                }
                Kind::Local => {
                    for _ in 0..n_ch {
                        let _ = rec.sample_ext();
                    }
                }
            }
        }
    }
    // observe_perm_and_sample_alpha.
    if let Some(perm_commit) = &p.commitments.permutation {
        rec.obs_cap(perm_commit);
        for data in p.global_lookup_data.iter().flatten() {
            rec.obs_ext(&data.cumulative_sum);
        }
    }
    let _alpha_constraints = rec.sample_ext();
    // observe_quotient_commitment; sample zeta.
    rec.obs_cap(&p.commitments.quotient_chunks);
    let zeta = rec.sample_ext();

    // ---- The PCS round structure (verify_batch's coms_to_verify) ----------
    let pcs = config.pcs();
    let ext_doms: Vec<OuterDomain> = p
        .degree_bits
        .iter()
        .map(|&db| outer_domain(pcs, 1usize << db))
        .collect();
    let zeta_nexts: Vec<EF> = ext_doms
        .iter()
        .map(|dom| {
            dom.next_point(zeta)
                .ok_or("next_point unavailable".to_string())
        })
        .collect::<Result<_, _>>()?;

    let mut coms: Vec<ComRound> = Vec::new();
    // The structural input-round shapes, built ALONGSIDE coms so the
    // (log_height, width, points, next-generator) tuples come from the same
    // objects the real pcs.verify consumes (self-check 1 below covers both).
    let mut input_rounds: Vec<FixtureInputRound> = Vec::new();
    let mat_shape = |domain: &OuterDomain, width: usize, num_points: usize, next_bits: usize| {
        FixtureInputMatrix {
            log_height: log2_strict(domain.size()) + OUTER_FRI_LOG_BLOWUP,
            width,
            num_points,
            next_point_bits: if num_points == 2 { next_bits } else { 0 },
        }
    };
    // Trace round.
    let mut trace_round = Vec::with_capacity(n);
    let mut trace_shape = Vec::with_capacity(n);
    for i in 0..n {
        let inst = &p.opened_values.instances[i].base_opened_values;
        let mut points = vec![(zeta, inst.trace_local.clone())];
        if let Some(next) = &inst.trace_next {
            points.push((zeta_nexts[i], next.clone()));
        }
        trace_shape.push(mat_shape(
            &ext_doms[i],
            inst.trace_local.len(),
            points.len(),
            p.degree_bits[i],
        ));
        trace_round.push((ext_doms[i], points));
    }
    coms.push((p.commitments.main.clone(), trace_round));
    input_rounds.push(FixtureInputRound {
        matrices: trace_shape,
    });
    // Quotient chunks round (natural domains of size 2^ext_db, flattened).
    let mut qc_round = Vec::new();
    let mut qc_shape = Vec::new();
    for i in 0..n {
        let inst = &p.opened_values.instances[i].base_opened_values;
        for chunk in &inst.quotient_chunks {
            qc_shape.push(mat_shape(&ext_doms[i], chunk.len(), 1, 0));
            qc_round.push((ext_doms[i], vec![(zeta, chunk.clone())]));
        }
    }
    coms.push((p.commitments.quotient_chunks.clone(), qc_round));
    input_rounds.push(FixtureInputRound { matrices: qc_shape });
    // Preprocessed round.
    if let Some(global) = &common.preprocessed {
        let mut pre_round = Vec::new();
        let mut pre_shape = Vec::new();
        for &inst_idx in &global.matrix_to_instance {
            let inst = &p.opened_values.instances[inst_idx].base_opened_values;
            let local = inst
                .preprocessed_local
                .as_ref()
                .ok_or("missing preprocessed_local for a preprocessed instance")?;
            let meta = global.instances[inst_idx]
                .as_ref()
                .ok_or("missing preprocessed metadata")?;
            let pre_domain = outer_domain(pcs, 1usize << meta.degree_bits);
            let mut points = vec![(zeta, local.clone())];
            if let Some(next) = &inst.preprocessed_next {
                points.push((zeta_nexts[inst_idx], next.clone()));
            }
            pre_shape.push(mat_shape(
                &pre_domain,
                local.len(),
                points.len(),
                p.degree_bits[inst_idx],
            ));
            pre_round.push((pre_domain, points));
        }
        coms.push((global.commitment.clone(), pre_round));
        input_rounds.push(FixtureInputRound {
            matrices: pre_shape,
        });
    }
    // Permutation round.
    if let Some(perm_commit) = &p.commitments.permutation {
        let mut perm_round = Vec::new();
        let mut perm_shape = Vec::new();
        for i in 0..n {
            let inst = &p.opened_values.instances[i];
            if !inst.permutation_local.is_empty() {
                perm_shape.push(mat_shape(
                    &ext_doms[i],
                    inst.permutation_local.len(),
                    2,
                    p.degree_bits[i],
                ));
                perm_round.push((
                    ext_doms[i],
                    vec![
                        (zeta, inst.permutation_local.clone()),
                        (zeta_nexts[i], inst.permutation_next.clone()),
                    ],
                ));
            }
        }
        coms.push((perm_commit.clone(), perm_round));
        input_rounds.push(FixtureInputRound {
            matrices: perm_shape,
        });
    }

    // ---- SELF-CHECK 1: the REAL pcs.verify accepts from the recorded state.
    // This validates every event recorded so far AND the round structure: the
    // pcs re-observes the opened values itself, samples alpha and the whole
    // FRI transcript, and re-checks all Merkle openings + the fold chains.
    {
        let mut ch = rec.ch.clone();
        <OuterPcsT as Pcs<EF, OuterChallenger>>::verify(
            pcs,
            coms.clone(),
            &p.opening_proof,
            &mut ch,
        )
        .map_err(|e| {
            format!(
                "REAL pcs.verify rejected from the mirrored transcript state \
                     (the prefix mirror or round structure diverges from verify_batch): {e:?}"
            )
        })?;
    }

    // pcs.verify's own opened-value observes (two_adic_pcs.rs:687-694), then
    // the FRI batch-combination alpha (verifier.rs:143).
    for (_, round) in &coms {
        for (_, mat) in round {
            for (_, values) in mat {
                for v in values {
                    rec.obs_ext(v);
                }
            }
        }
    }
    let alpha = rec.sample_ext();

    let prefix_events = rec.events;
    let ch0 = rec.ch; // positioned at the FRI commit phase

    // ---- Phase B: the FRI core, exactly as the gnark circuit will run it ---
    let fri = &p.opening_proof;
    let rounds = fri.commit_phase_commits.len();
    if fri.commit_pow_witnesses.len() != rounds {
        return Err("commit PoW witness count mismatch".into());
    }
    if fri.query_proofs.len() != OUTER_FRI_NUM_QUERIES {
        return Err(format!(
            "expected {OUTER_FRI_NUM_QUERIES} query proofs, got {}",
            fri.query_proofs.len()
        ));
    }
    for qp in &fri.query_proofs {
        if qp.commit_phase_openings.len() != rounds {
            return Err("query has wrong number of commit-phase openings".into());
        }
        for step in &qp.commit_phase_openings {
            if step.log_arity != 1 || step.sibling_values.len() != 1 {
                return Err("non-arity-2 commit round (fixture scope is arity 2)".into());
            }
        }
    }
    let log_global_max_height = rounds + OUTER_FRI_LOG_BLOWUP; // log_final_poly_len = 0
    let max_db = *p.degree_bits.iter().max().ok_or("no instances")?;
    if max_db + OUTER_FRI_LOG_BLOWUP != log_global_max_height {
        return Err(format!(
            "round count {rounds} inconsistent with max degree bits {max_db} + blowup {OUTER_FRI_LOG_BLOWUP}"
        ));
    }
    if fri.final_poly.len() != 1 {
        return Err("expected a constant final polynomial (log_final_poly_len = 0)".into());
    }

    // Real MMCSes for host-side re-verification (identical constants to the
    // config's own — dregg_poseidon2_bn254 is deterministic).
    let perm = dregg_poseidon2_bn254();
    let val_mmcs = OuterValMmcs::new(
        OuterHash::new(perm.clone()).map_err(|e| format!("{e:?}"))?,
        OuterCompress::new(perm),
        0,
    );
    let challenge_mmcs = OuterChallengeMmcs::new(val_mmcs.clone());
    let folding: TwoAdicFriFolding<
        Vec<BatchOpening<BabyBear, OuterValMmcs>>,
        <OuterValMmcs as Mmcs<BabyBear>>::Error,
    > = TwoAdicFriFolding(core::marker::PhantomData);

    let mut ch = ch0;
    let mut betas: Vec<EF> = Vec::with_capacity(rounds);
    for comm in &fri.commit_phase_commits {
        ch.observe(comm.clone());
        // commit_proof_of_work_bits = 0: check_witness is a no-op.
        betas.push(ch.sample_algebra_element());
    }
    ch.observe_algebra_slice(&fri.final_poly);
    for _ in 0..rounds {
        ch.observe(BabyBear::ONE); // the arity schedule (log_arity = 1)
    }
    if !ch.check_witness(OUTER_FRI_QUERY_POW_BITS, fri.query_pow_witness) {
        return Err("query PoW witness failed host-side check".into());
    }

    let mut roll_in_rounds: Option<Vec<usize>> = None;
    let mut queries_out: Vec<FixtureQuery> = Vec::with_capacity(fri.query_proofs.len());

    for (qi, qp) in fri.query_proofs.iter().enumerate() {
        let index = ch.sample_bits(log_global_max_height); // extra_query_index_bits = 0
        let ro = open_input_replica(
            OUTER_FRI_LOG_BLOWUP,
            log_global_max_height,
            index,
            &qp.input_proof,
            alpha,
            &val_mmcs,
            &coms,
        )?;
        if ro.first().map(|(lh, _)| *lh) != Some(log_global_max_height) {
            return Err(format!(
                "query {qi}: initial reduced opening not at max height"
            ));
        }
        let initial_eval = ro[0].1;

        // Serialize the input-batch openings (already host-verified by the
        // real val_mmcs.verify_batch inside open_input_replica), shape-checked
        // against the structural input_rounds.
        if qp.input_proof.len() != input_rounds.len() {
            return Err(format!(
                "query {qi}: {} input batches for {} structural rounds",
                qp.input_proof.len(),
                input_rounds.len()
            ));
        }
        let mut input_openings: Vec<FixtureInputBatch> = Vec::with_capacity(qp.input_proof.len());
        for (ri, (batch, round_shape)) in qp.input_proof.iter().zip(input_rounds.iter()).enumerate()
        {
            if batch.opened_values.len() != round_shape.matrices.len() {
                return Err(format!(
                    "query {qi} input round {ri}: {} opened rows for {} matrices",
                    batch.opened_values.len(),
                    round_shape.matrices.len()
                ));
            }
            for (row, m) in batch.opened_values.iter().zip(&round_shape.matrices) {
                if row.len() != m.width {
                    return Err(format!(
                        "query {qi} input round {ri}: row width {} != matrix width {}",
                        row.len(),
                        m.width
                    ));
                }
            }
            let max_lh = round_shape
                .matrices
                .iter()
                .map(|m| m.log_height)
                .max()
                .ok_or("empty input round")?;
            if batch.opening_proof.len() != max_lh {
                return Err(format!(
                    "query {qi} input round {ri}: path has {} levels, tree height is {max_lh}",
                    batch.opening_proof.len()
                ));
            }
            input_openings.push(FixtureInputBatch {
                rows: batch
                    .opened_values
                    .iter()
                    .map(|row| row.iter().map(bb_u32).collect())
                    .collect(),
                path: batch
                    .opening_proof
                    .iter()
                    .map(|d| bn254_hex(&d[0]))
                    .collect(),
            });
        }
        let mut ro_iter = ro[1..].iter().peekable();

        let mut folded = initial_eval;
        let mut domain_index = index;
        let mut log_current = log_global_max_height;
        let mut q_roll_rounds: Vec<usize> = Vec::new();
        let mut q_roll_vals: Vec<EF> = Vec::new();
        let mut siblings: Vec<[u32; 4]> = Vec::with_capacity(rounds);
        let mut merkle_paths: Vec<Vec<String>> = Vec::with_capacity(rounds);

        for (r, step) in qp.commit_phase_openings.iter().enumerate() {
            let sib = step.sibling_values[0];
            let bit = domain_index & 1;
            let evals: Vec<EF> = if bit == 0 {
                vec![folded, sib]
            } else {
                vec![sib, folded]
            };
            domain_index >>= 1;
            let log_folded = log_current - 1;

            challenge_mmcs
                .verify_batch(
                    &fri.commit_phase_commits[r],
                    &[Dimensions {
                        width: 2,
                        height: 1 << log_folded,
                    }],
                    domain_index,
                    BatchOpeningRef::new(core::slice::from_ref(&evals), &step.opening_proof),
                )
                .map_err(|e| {
                    format!("query {qi} round {r}: commit-phase Merkle opening failed: {e:?}")
                })?;

            folded = <TwoAdicFriFolding<_, _> as FriFoldingStrategy<BabyBear, EF>>::fold_row(
                &folding,
                domain_index,
                log_folded,
                1,
                betas[r],
                evals.into_iter(),
            );
            log_current = log_folded;

            if let Some((_, v)) = ro_iter.next_if(|(lh, _)| *lh == log_current) {
                folded += betas[r] * betas[r] * *v; // beta^arity = beta^2
                q_roll_rounds.push(r);
                q_roll_vals.push(*v);
            }

            siblings.push(ef_coords(&sib));
            merkle_paths.push(
                step.opening_proof
                    .iter()
                    .map(|d| bn254_hex(&d[0]))
                    .collect(),
            );
        }
        if log_current != OUTER_FRI_LOG_BLOWUP {
            return Err(format!("query {qi}: fold ended at height {log_current}"));
        }
        if ro_iter.next().is_some() {
            return Err(format!("query {qi}: unconsumed reduced openings"));
        }
        // final_poly is a constant: its evaluation at any x is coefficient 0.
        if folded != fri.final_poly[0] {
            return Err(format!(
                "query {qi}: fold chain does not reach the final polynomial \
                 (transcript or reduced-opening replica diverges)"
            ));
        }
        match &roll_in_rounds {
            None => roll_in_rounds = Some(q_roll_rounds.clone()),
            Some(expected) if *expected != q_roll_rounds => {
                return Err("roll-in schedule differs across queries".into());
            }
            _ => {}
        }
        queries_out.push(FixtureQuery {
            expected_index: index as u64,
            initial_eval: ef_coords(&initial_eval),
            roll_ins: q_roll_vals.iter().map(ef_coords).collect(),
            siblings,
            merkle_paths,
            input_openings,
        });
    }

    Ok(RealShrinkFriFixture {
        version: 4,
        description: "REAL dregg apex shrink proof (BatchStarkProof<DreggOuterConfig> over a real \
                      ir2_leaf_wrap apex) WITH the 25-lane chain claim AND the 8-lane apex \
                      VK-core (the apex's preprocessed commitment, in-circuit pinned via \
                      pin_preprocessed_commit) re-exposed through the shrink proof's own \
                      expose_claim table (shrink_apex_to_outer_exposed): pre-FRI transcript \
                      events + per-instance table public values + FRI commit-phase data + \
                      per-query INPUT-BATCH openings (open_input) for the chain/gnark native \
                      verifier."
            .into(),
        degree_bits: p.degree_bits.clone(),
        table_publics: publics
            .iter()
            .map(|pv| pv.iter().map(bb_u32).collect())
            .collect(),
        claim_instance,
        apex_preprocessed_commit,
        fri: FixtureFriShape {
            log_blowup: OUTER_FRI_LOG_BLOWUP,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: OUTER_FRI_NUM_QUERIES,
            commit_pow_bits: 0,
            query_pow_bits: OUTER_FRI_QUERY_POW_BITS,
            extra_query_index_bits: 0,
            rounds,
            log_global_max_height,
        },
        prefix_events,
        commit_roots: fri
            .commit_phase_commits
            .iter()
            .map(|cap| {
                let roots = cap.roots();
                assert_eq!(roots.len(), 1, "cap_height 0 ⇒ single root");
                bn254_hex(&roots[0][0])
            })
            .collect(),
        expected_betas: betas.iter().map(ef_coords).collect(),
        final_poly: fri.final_poly.iter().map(ef_coords).collect(),
        query_pow_witness: bb_u32(&fri.query_pow_witness),
        roll_in_rounds: roll_in_rounds.unwrap_or_default(),
        input_rounds,
        queries: queries_out,
    })
}
