//! THE REAL LEAF: the Lean-descriptor EffectVM AIR (`EffectVmDescriptorAir`) proven as a
//! recursion-compatible uni-STARK over the REAL execution trace, then verified IN-CIRCUIT
//! by the emberian p3-recursion fork (`build_and_prove_next_layer`).
//!
//! This is the engine-level witness for the whole-chain IVC cutover
//! (`ivc_turn_chain::prove_turn_chain_recursive`): the leaves the chain fold wraps are no
//! longer `EffectVmShapeAir` stubs but the full descriptor constraint set — Poseidon2
//! state-commit hash sites, transition continuity, PI bindings (OLD/NEW_COMMIT), range
//! checks — so a forged `(old_root, new_root)` has NO satisfying leaf and the wrap fails.
//!
//! Run: `cargo test -p dregg-circuit --test descriptor_leaf_recursion -- --nocapture`
//! (recursion proving is slow; each wrap compiles + proves a verifier circuit).

#![cfg(feature = "recursion")]

use std::time::Instant;

use dregg_circuit::effect_vm::columns::sel;
use dregg_circuit::effect_vm::{CellState, Effect, generate_effect_vm_trace, pi};
use dregg_circuit::effect_vm_descriptors::descriptor_for_selector;
use dregg_circuit::lean_descriptor_air::{
    EffectVmDescriptorAir, descriptor_recursion_matrix, parse_vm_descriptor,
};
use dregg_circuit::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, create_recursion_config, prove_inner_for_air,
    verify_inner_for_air, verify_recursive_batch_proof,
};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing as _;
use p3_recursion::{ProveNextLayerParams, RecursionInput, build_and_prove_next_layer};

const D: usize = 4;

fn to_p3(v: dregg_circuit::field::BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

/// One real transfer turn: descriptor-AIR uni-stark leaf proven over the genuine
/// 186-column EffectVM trace, wrapped in-circuit, root verified.
#[test]
fn descriptor_leaf_proves_and_wraps_in_circuit() {
    let json = descriptor_for_selector(sel::TRANSFER).expect("transfer descriptor registered");
    let desc = parse_vm_descriptor(json).expect("transfer descriptor parses");

    let state = CellState::new(1000, 0);
    let effects = vec![Effect::Transfer {
        amount: 7,
        direction: 1,
    }];
    let (base_trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
    eprintln!(
        "base trace: {} rows x {} cols; descriptor air width {} (pi_count {})",
        base_trace.len(),
        base_trace[0].len(),
        desc.trace_width,
        desc.public_input_count
    );
    let dpis = &public_inputs[..desc.public_input_count];

    let t0 = Instant::now();
    let matrix = descriptor_recursion_matrix(&desc, &base_trace).expect("extend trace");
    eprintln!(
        "extended matrix: {} cols ({:?})",
        matrix.width,
        t0.elapsed()
    );

    let air = EffectVmDescriptorAir::new(desc.clone());

    let t1 = Instant::now();
    let inner = prove_inner_for_air(&air, matrix, dpis);
    eprintln!("inner uni-stark prove: {:?}", t1.elapsed());

    let t2 = Instant::now();
    verify_inner_for_air(&air, &inner, dpis).expect("inner descriptor uni-stark verifies");
    eprintln!("inner verify: {:?}", t2.elapsed());

    // Wrap: in-circuit verification of the descriptor leaf.
    let config = create_recursion_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();
    let p3_pis: Vec<P3BabyBear> = dpis.iter().map(|&v| to_p3(v)).collect();
    let input = RecursionInput::UniStark {
        proof: &inner,
        air: &air,
        public_inputs: p3_pis,
        preprocessed_commit: None,
    };
    let t3 = Instant::now();
    let wrapped = build_and_prove_next_layer::<DreggRecursionConfig, EffectVmDescriptorAir, _, D>(
        &input, &config, &backend, &params,
    )
    .expect("descriptor leaf wraps into an in-circuit recursive layer");
    eprintln!("leaf wrap (in-circuit verify + prove): {:?}", t3.elapsed());

    let t4 = Instant::now();
    verify_recursive_batch_proof(&wrapped.0).expect("wrapped leaf batch proof verifies");
    eprintln!("wrapped batch verify: {:?}", t4.elapsed());

    // Sanity: the PI prefix genuinely carries the roots the chain binds.
    assert_eq!(dpis[pi::OLD_COMMIT], public_inputs[pi::OLD_COMMIT]);
    assert_eq!(dpis[pi::NEW_COMMIT], public_inputs[pi::NEW_COMMIT]);
}
