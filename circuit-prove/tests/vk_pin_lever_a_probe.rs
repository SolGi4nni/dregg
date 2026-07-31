//! **FALSIFICATION PROBE — lever (a): does the VK-identity pin reach the ROOT fingerprint?**
//!
//! Two comments in this repo disagree about the same object:
//!
//! * `ivc_turn_chain.rs:171-183` — "**Child-circuit identity under the VK pin (fork
//!   follow-up — CLOSED)**. … A foreign-circuit child is refused in-band either way — keep
//!   the honest constant and the foreign child's in-circuit preprocessed-trace FRI check is
//!   UNSAT …; **bake the foreign commitment and the parent op-list changes, so the ROOT
//!   preprocessed commitment changes and the root VK fingerprint (tooth 1) stops matching
//!   the honest anchor.**"
//! * `plonky3_recursion_impl.rs:705-713` — "Does NOT (cannot, harness-side) pin: the
//!   **child** proofs' circuit identity."
//!
//! An audit said the older comment is right. The load-bearing half is the SECOND horn: does
//! baking a different commitment change the parent's op-list *as the preprocessed
//! commitment sees it*? This probe measures that on the deployed pin path.
//!
//! Two measurements, both cheap:
//!
//! **(A) What the deployed pin actually bakes.** `batch_to_pinned_input`
//! (`ivc_turn_chain.rs:4757`) and `merge_two_segment_proofs` (`:4816`) read the expected
//! cap OFF THE CHILD PROOF (`child.stark_common.preprocessed.commitment`). So the question
//! "can two different children share one cap" decides whether that pin can discriminate at
//! all. Measured against the two lever-(a) children of `const_pin_probe.rs` (same shape,
//! different constant).
//!
//! **(B) Whether the baked value reaches the parent's VK core.** Build the parent verifier
//! circuit TWICE over the SAME child, with `expected_preprocessed_commit` set to the honest
//! cap and to a perturbed one, then run the fold's own
//! `build_next_layer_prep` — the exact helper `prove_next_layer` uses to compute the layer's
//! preprocessed commitment — and compare. No parent proof is needed: the preprocessed
//! commitment is a function of the op-list alone, which is precisely what the disputed
//! sentence claims changes.
//!
//! `recursion_vk_fingerprint` hashes shape + `preprocessed.commitment`, so equal shape and
//! equal commitment IS an equal fingerprint.
//!
//! ## ⚑ BOTH ASSERTIONS INVERTED 2026-07-30 — THE OLDER COMMENT WINS, AFTER A SUBSTRATE FIX
//!
//! Measured at `bb42f9800`, the audit was right on both counts. It is now wrong on both, because
//! the substrate its premise rested on changed: fork commit `fc3c6df`
//! (`emberian/plonky3-recursion`) moved a constant's VALUE into `ConstAir`'s preprocessed row
//! (`[ext_mult, out_idx, value[0..D]]`, was `[ext_mult, out_idx]`) and added `D` degree-1
//! constraints `main.value[i] == prep.value[i]`.
//!
//! Since lever (a) bakes the expected cap as `alloc_const` values, those values are now
//! preprocessed columns of the PARENT, so the parent's preprocessed commitment depends on WHICH
//! cap was baked. MEASURED at the new rev, and note what is IDENTICAL in it:
//!
//! ```text
//!   [honest  cap] parent prep cap = [[1233588605, 1402159262, 830122016, 730413766, …]]
//!   [foreign cap] parent prep cap = [[1128576629, 1286127648, 223558623, 1010029691, …]]
//!   both: instances (width, degree_bits) = [(6,7), (2,6), (59,13), (24,11), (2,12)]
//!   both: public_flat_len = 51
//! ```
//!
//! Every SHAPE field `recursion_vk_fingerprint` hashes is the same on both sides; only the
//! preprocessed commitment differs. So this is the separation happening through the commitment
//! itself rather than through a row count — the distinction `vk_spine_forgery_probe.rs` flagged
//! as undemonstrated in its three-op miniature.
//!
//! The `(6, 7)` first instance is the Const table at its new width: `2 + D` with `D = 4`.
//!
//! Both assertions were flipped by writing the opposite claim and re-running. The circuits, the
//! `build_next_layer_prep` call and the no-pin control are byte-unchanged.

use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, create_recursion_config,
    recursion_vk_fingerprint,
};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::ProverData;
use p3_circuit::CircuitBuilder;
use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep};
use p3_circuit_prover::{
    AirVariant, BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile,
    TablePacking,
};
use p3_commit::Pcs;
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, build_next_layer_circuit,
    build_next_layer_prep,
};

use p3_uni_stark::StarkGenericConfig;

const D: usize = 4;
const DIGEST_ELEMS: usize = 8;
type EF = BinomialExtensionField<P3BabyBear, D>;

/// The runtime preprocessed-commitment (Merkle cap) type — the VK-identity core lever (a)
/// pins. Mirrors `ivc_turn_chain::RecursionCommit`, which is `pub(crate)`.
type Commit = <<DreggRecursionConfig as StarkGenericConfig>::Pcs as Pcs<
    <DreggRecursionConfig as StarkGenericConfig>::Challenge,
    <DreggRecursionConfig as StarkGenericConfig>::Challenger,
>>::Commitment;

/// The lever-(a) shape at constant `k` — one public input, one `alloc_const(k)`,
/// `connect(t, k)`: the two lines `pin_preprocessed_commit` emits per cap element.
fn prove_lever_a_shape(k: u32) -> BatchStarkProof<DreggRecursionConfig> {
    let mut cb = CircuitBuilder::<EF>::new();
    let t = cb.alloc_public_input("child VK cap target");
    let expected_const = cb.alloc_const(EF::from_u32(k), "VK-identity pin (expected child VK cap)");
    cb.connect(t, expected_const);
    let circuit = cb.build().expect("the two-op lever-(a) circuit builds");

    let packing = TablePacking::new(4, 4);
    let config = create_recursion_config();
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> = vec![];
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<DreggRecursionConfig, EF, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .expect("table-AIR extraction");
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();

    let mut runner = circuit.runner();
    runner
        .set_public_inputs(&[EF::from_u32(k)])
        .expect("one public input");
    let traces = runner.run().expect("witness generation");

    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let cpd = CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    let prover = BatchStarkProver::new(config)
        .with_table_packing(packing)
        .with_alu_variant(AirVariant::Baseline);
    prover
        .prove_all_tables(&traces, &cpd)
        .expect("the two-op circuit proves")
}

fn cap_of(proof: &BatchStarkProof<DreggRecursionConfig>) -> Commit {
    proof
        .stark_common
        .preprocessed
        .as_ref()
        .expect("the child carries a preprocessed commitment (its VK core)")
        .commitment
        .clone()
}

/// The cap's flat digest words. `cap_height = 0` for this config, so a cap is one digest.
fn cap_lanes(c: &Commit) -> Vec<[P3BabyBear; DIGEST_ELEMS]> {
    c.roots().to_vec()
}

/// **(A)** The deployed pin reads the expected cap OFF THE CHILD. Measure whether two
/// children that differ ONLY in a `define_const` value present the same cap — i.e. whether
/// that pin can discriminate them at all.
///
/// ⚑ It can, as of fork rev `fc3c6df`. The assertion asserts the separation, so it goes red if
/// const values ever leave the preprocessed trace again.
#[test]
fn two_children_differing_only_in_a_const_present_two_vk_caps() {
    let child7 = prove_lever_a_shape(7);
    let child9 = prove_lever_a_shape(9);
    let cap7 = cap_of(&child7);
    let cap9 = cap_of(&child9);
    println!("child k=7 cap: {:?}", cap_lanes(&cap7));
    println!("child k=9 cap: {:?}", cap_lanes(&cap9));
    println!("caps equal: {}", cap_lanes(&cap7) == cap_lanes(&cap9));
    println!(
        "child fingerprints equal: {}",
        recursion_vk_fingerprint(&child7) == recursion_vk_fingerprint(&child9)
    );
    assert_ne!(
        cap_lanes(&cap7),
        cap_lanes(&cap9),
        "THE CLOSE FAILED: two children differing ONLY in a `define_const` value present ONE VK \
         cap, so the deployed pin — which reads the expected cap off the child — cannot \
         discriminate a const-level lie at all."
    );
}

/// **(B)** Build the parent verifier circuit twice over the SAME child, differing only in
/// the value lever (a) bakes, and compare the parent's VK core (its preprocessed
/// commitment) plus the shape fields `recursion_vk_fingerprint` hashes.
///
/// The disputed sentence predicts these DIFFER ("the parent op-list changes, so the ROOT
/// preprocessed commitment changes"). The audit predicts they are identical.
///
/// ⚑ The disputed sentence WINS as of fork rev `fc3c6df` — the baked cap is `alloc_const`
/// material and const values are now preprocessed columns. It did NOT win at `bb42f9800`; the
/// sentence was true of a substrate that did not yet exist.
#[test]
fn baking_a_different_cap_moves_the_parent_vk_core() {
    let child = prove_lever_a_shape(7);
    let honest = cap_of(&child);
    let mut roots = cap_lanes(&honest);
    roots[0][0] += P3BabyBear::ONE;
    roots[0][3] += P3BabyBear::from_u32(12345);
    let foreign: Commit = Commit::new(roots);
    assert_ne!(
        cap_lanes(&honest),
        cap_lanes(&foreign),
        "the perturbed cap must differ (else the probe measured nothing)"
    );

    // The `table_public_inputs` threading `batch_to_pinned_input` performs (lever (b)).
    let num_primitive = p3_circuit_prover::batch_stark_prover::NUM_PRIMITIVE_TABLES;
    let mut tpi: Vec<Vec<P3BabyBear>> = vec![Vec::new(); num_primitive];
    for entry in &child.non_primitives {
        tpi.push(entry.public_values.clone());
    }

    let config = create_recursion_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // THE POSITIVE CONTROL is the third row: `expected_preprocessed_commit: None` drops the
    // pin's 8 `alloc_const` + `connect` pairs entirely. If the instrument cannot even see
    // THAT, it is blind to the op-list and nothing above is attributable.
    let mut results = Vec::new();
    for (label, cap) in [
        ("honest cap", Some(honest)),
        ("foreign cap", Some(foreign)),
        ("NO PIN (control)", None),
    ] {
        let input: RecursionInput<'_, DreggRecursionConfig, BatchOnly> =
            RecursionInput::BatchStark {
                proof: &child,
                common_data: &child.stark_common,
                table_public_inputs: tpi.clone(),
                expected_preprocessed_commit: cap,
            };
        let (circuit, _vr) = build_next_layer_circuit::<DreggRecursionConfig, BatchOnly, _, D>(
            &input, &config, &backend,
        )
        .expect("the parent verifier circuit builds");
        let prep = build_next_layer_prep::<DreggRecursionConfig, BatchOnly, _, D>(
            &circuit, &config, &backend, &params,
        )
        .expect("the parent preprocessed commitment computes");
        let common = prep.circuit_prover_data.common_data();
        let parent_cap = common
            .preprocessed
            .as_ref()
            .map(|gp| cap_lanes(&gp.commitment));
        let widths: Vec<(usize, usize)> = common
            .preprocessed
            .as_ref()
            .map(|gp| {
                gp.instances
                    .iter()
                    .map(|i| i.as_ref().map_or((0, 0), |m| (m.width, m.degree_bits)))
                    .collect()
            })
            .unwrap_or_default();
        println!(
            "[{label}] parent public_flat_len = {}",
            circuit.public_flat_len
        );
        println!("[{label}] parent preprocessed cap = {parent_cap:?}");
        println!("[{label}] parent preprocessed instance (width, degree_bits) = {widths:?}");
        results.push((parent_cap, widths, circuit.public_flat_len));
    }

    let (honest_r, foreign_r, unpinned_r) = (&results[0], &results[1], &results[2]);
    println!(
        "\nparent VK core identical across the two baked caps: {}",
        honest_r == foreign_r
    );
    println!(
        "parent VK core sensitive to the pin EXISTING at all: {}",
        honest_r != unpinned_r
    );

    // NOT ATTRIBUTABLE unless the instrument can go red.
    assert_ne!(
        honest_r, unpinned_r,
        "NOT ATTRIBUTABLE: dropping the pin entirely did not move the parent's VK core \
         either — this instrument is blind to the op-list, so its verdict on the pin's \
         VALUE means nothing"
    );

    assert_ne!(
        honest_r, foreign_r,
        "HORN 2 REOPENED: baking a DIFFERENT cap left the parent's VK core untouched, so lever \
         (a) pins nothing that reaches the root fingerprint and a foreign child is invisible to \
         verify tooth (1). This held at `bb42f9800` and must not hold again."
    );
}
