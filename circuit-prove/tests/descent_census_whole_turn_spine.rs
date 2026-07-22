//! Exact Descent census over a heterogeneous SetField→Custom cohort chain.
//!
//! This is deliberately a heavy production-mechanism gate: it mints the real
//! HidingFri census, re-proves its Lean-emitted IR2 relation inside recursion,
//! and binds it to a three-leg stand-in for the narrow heterogeneous turn:
//! ordinary SetField writes followed by a no-op terminal Custom sentinel.  The
//! sentinel uses the deployed Custom-wide PI geometry, including its existing
//! AFTER-field and exact fields-root exposure.  No hypothetical ordinary
//! SetField exposure is assumed.  The remaining live cutover is the
//! verifier-committed placement policy and SDK emission of that sentinel.

use std::collections::BTreeMap;

use dregg_cell::{FieldElement, field_from_u64};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, VmConstraint2,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};
use dregg_circuit::refusal::must_refuse;
use dregg_circuit_prove::custom_cohort_spine::{
    prove_direct_ir2_whole_turn_binding_node_segmented, prove_segment_merge_preserving_claims,
    terminal_custom_suffix_len,
};
use dregg_circuit_prove::custom_leaf_adapter::prove_direct_ir2_leaf_with_app_and_fields_root_commitment;
use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
use dregg_circuit_prove::descent_census;
use dregg_circuit_prove::ivc_turn_chain::{
    CUSTOM_PROGRAM_VK_PI_LO, SEG_ANCHOR_WIDTH, SEG_WIDTH, ir2_leaf_wrap_config,
    prove_descriptor_leaf_expose_segment_and_claims, prove_descriptor_leaf_rotated_with_segment,
};
use dregg_circuit_prove::joint_turn_recursive::{CUSTOM_COMMIT_LEN, CUSTOM_COMMIT_PI_LO};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::DreggRecursionConfig;
use p3_field::PrimeField32;
use p3_recursion::RecursionOutput;

const APP_LEN: usize = 6;
// Current Custom-wide geometry:
// 46 rotated + commitment/VK exposure 16 + dsl-rc 4 + field octet 8 +
// fields_root8 + old/new anchors 16 = 98.
const ORDINARY_WIDE_PI_COUNT: usize = 66;
const CUSTOM_WIDE_PI_COUNT: usize = 98;
const FIELD_OCTET_PI_LO: usize = 66;
const FIELDS_ROOT_PI_LO: usize = 74;

fn root8(base: u32) -> [BabyBear; 8] {
    core::array::from_fn(|lane| BabyBear::new(base + lane as u32))
}

/// Minimal FRI-bound wide cohort leg. `claims` are `(PI offset, lanes)`;
/// `claim_slices` selects their order after the ordinary segment.
fn wide_leg(
    name: &str,
    pi_count: usize,
    old8: [BabyBear; 8],
    new8: [BabyBear; 8],
    claims: &[(usize, Vec<BabyBear>)],
    claim_slices: &[(usize, usize)],
    config: &DreggRecursionConfig,
) -> RecursionOutput<DreggRecursionConfig> {
    assert!(pi_count >= ORDINARY_WIDE_PI_COUNT);
    let old_pi_lo = pi_count - 2 * SEG_ANCHOR_WIDTH;
    let new_pi_lo = pi_count - SEG_ANCHOR_WIDTH;
    let mut pinned = BTreeMap::<usize, BabyBear>::new();
    for (offset, values) in claims {
        for (lane, value) in values.iter().copied().enumerate() {
            let prior = pinned.insert(offset + lane, value);
            assert!(prior.is_none(), "stand-in claim PI slices must not overlap");
        }
    }
    for lane in 0..8 {
        assert!(pinned.insert(old_pi_lo + lane, old8[lane]).is_none());
        assert!(pinned.insert(new_pi_lo + lane, new8[lane]).is_none());
    }

    let mut public_inputs = vec![BabyBear::ZERO; pi_count];
    let mut row = Vec::with_capacity(pinned.len());
    let mut constraints = Vec::with_capacity(pinned.len());
    for (col, (&pi_index, &value)) in pinned.iter().enumerate() {
        public_inputs[pi_index] = value;
        row.push(value);
        constraints.push(VmConstraint2::Base(VmConstraint::PiBinding {
            row: VmRow::First,
            col,
            pi_index,
        }));
    }

    let descriptor = EffectVmDescriptor2 {
        name: name.to_string(),
        trace_width: row.len(),
        public_input_count: pi_count,
        tables: vec![],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    };
    let trace = (0..4).map(|_| row.clone()).collect::<Vec<_>>();
    let proof = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &descriptor,
        &trace,
        &public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        config,
    )
    .expect("stand-in wide cohort descriptor proves");
    if claim_slices.is_empty() {
        prove_descriptor_leaf_rotated_with_segment(&descriptor, &proof, &public_inputs, config)
            .expect("ordinary wide cohort leaf exposes its segment")
    } else {
        prove_descriptor_leaf_expose_segment_and_claims(
            &descriptor,
            &proof,
            &public_inputs,
            config,
            claim_slices,
        )
        .expect("wide cohort leaf exposes its segment and selected claims")
    }
}

fn custody_fields() -> BTreeMap<u64, FieldElement> {
    descent_census::RELIC_KEYS
        .into_iter()
        .zip([1, 8, 8, 9, 2, 3, 4, 9])
        .map(|(key, code)| (key, field_from_u64(code)))
        .collect()
}

#[test]
#[ignore = "heavy: real hiding census + direct IR2 recursion + terminal-Custom cohort spine"]
fn exact_census_binds_to_setfield_prefix_and_terminal_custom() {
    let config = ir2_leaf_wrap_config();
    let old8 = root8(100);
    let after_first_write8 = root8(200);
    let final8 = root8(400);
    let old_u32 = old8.map(BabyBear::as_u32);
    let final_u32 = final8.map(BabyBear::as_u32);

    let (_hiding_proof, statement, bundle) =
        descent_census::prove_zk(&custody_fields(), old_u32, final_u32)
            .expect("the exact fixed-eight census proves under HidingFri");
    assert_eq!(statement.counts, [2, 2, 1, 1, 1, 1]);

    let direct = prove_direct_ir2_leaf_with_app_and_fields_root_commitment(
        &bundle.descriptor,
        &bundle.base_trace,
        &bundle.public_inputs,
        &bundle.vk_recipe,
        &bundle.app_root_binding,
        &bundle
            .post_fields_root_binding
            .expect("Descent census authenticates its exact fields root"),
        &config,
    )
    .expect("the exact census re-proves as a direct recursion leaf");

    let commitment = custom_proof_pi_commitment(&bundle.public_inputs);
    let vk8 = bundle.vk_recipe.canonical_vk_felts();
    let first_write = wide_leg(
        "descent-first-setfield-standin",
        ORDINARY_WIDE_PI_COUNT,
        old8,
        after_first_write8,
        &[],
        &[],
        &config,
    );

    let final_write = wide_leg(
        "descent-final-setfield-standin",
        ORDINARY_WIDE_PI_COUNT,
        after_first_write8,
        final8,
        &[],
        &[],
        &config,
    );

    let app = statement.counts.map(BabyBear::new);
    let fields_root = statement.post_fields_root.map(BabyBear::new);
    let terminal_custom = wide_leg(
        "descent-terminal-custom-standin",
        CUSTOM_WIDE_PI_COUNT,
        final8,
        final8,
        &[
            (CUSTOM_COMMIT_PI_LO, commitment.to_vec()),
            (CUSTOM_PROGRAM_VK_PI_LO, vk8.to_vec()),
            (FIELD_OCTET_PI_LO, app.to_vec()),
            (FIELDS_ROOT_PI_LO, fields_root.to_vec()),
        ],
        &[
            (CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN),
            (CUSTOM_PROGRAM_VK_PI_LO, 8),
            (FIELD_OCTET_PI_LO, APP_LEN),
            (FIELDS_ROOT_PI_LO, 8),
        ],
        &config,
    );

    let prefix = prove_segment_merge_preserving_claims(&first_write, 0, &final_write, 0, &config)
        .expect("the ordinary SetField prefix preserves exact state continuity");
    let whole_carrier = prove_segment_merge_preserving_claims(
        &prefix,
        0,
        &terminal_custom,
        terminal_custom_suffix_len(APP_LEN),
        &config,
    )
    .expect("the spine preserves terminal Custom identity and application state");
    let bound = prove_direct_ir2_whole_turn_binding_node_segmented(
        &whole_carrier,
        &direct,
        &config,
        APP_LEN,
    )
    .expect("the direct census binds to the complete heterogeneous transition");

    let exposed = bound
        .0
        .non_primitives
        .iter()
        .find(|entry| entry.op_type.as_str() == "expose_claim")
        .expect("bound whole turn re-exposes its ordinary chain segment");
    assert_eq!(exposed.public_values.len(), SEG_WIDTH);
    let lanes = exposed
        .public_values
        .iter()
        .map(|value| value.as_canonical_u32())
        .collect::<Vec<_>>();
    assert_eq!(&lanes[..8], &old_u32);
    assert_eq!(&lanes[8..16], &final_u32);

    // Hostile pole: the EffectVM chain itself may validly commit a different
    // terminal field value, but it must not be possible to staple the genuine
    // census proof onto that different state. The conflict happens in the final
    // recursion node's app-field connect, not in an off-circuit comparison.
    let mut wrong_app = app;
    wrong_app[0] += BabyBear::ONE;
    let wrong_terminal_custom = wide_leg(
        "descent-terminal-custom-wrong-count-standin",
        CUSTOM_WIDE_PI_COUNT,
        final8,
        final8,
        &[
            (CUSTOM_COMMIT_PI_LO, commitment.to_vec()),
            (CUSTOM_PROGRAM_VK_PI_LO, vk8.to_vec()),
            (FIELD_OCTET_PI_LO, wrong_app.to_vec()),
            (FIELDS_ROOT_PI_LO, fields_root.to_vec()),
        ],
        &[
            (CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN),
            (CUSTOM_PROGRAM_VK_PI_LO, 8),
            (FIELD_OCTET_PI_LO, APP_LEN),
            (FIELDS_ROOT_PI_LO, 8),
        ],
        &config,
    );
    let wrong_carrier = prove_segment_merge_preserving_claims(
        &prefix,
        0,
        &wrong_terminal_custom,
        terminal_custom_suffix_len(APP_LEN),
        &config,
    )
    .expect("the cohort spine faithfully preserves the wrong committed field");
    must_refuse("wrong terminal census field", || {
        prove_direct_ir2_whole_turn_binding_node_segmented(
            &wrong_carrier,
            &direct,
            &config,
            APP_LEN,
        )
    });
}
