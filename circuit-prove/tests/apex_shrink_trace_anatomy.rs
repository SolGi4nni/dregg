//! TRACE ANATOMY of the BN254-native shrink prove — the measurement harness
//! behind docs/deos/APEX-VERIFIER-AIR-REDUCTION.md.
//!
//! The real shrink run (tests/apex_shrink_bn254_tooth.rs, 2026-07-12) measured
//! degree_bits [9,9,15,14,15] and a ~18min prove at blowup 64. This test
//! answers WHY at the AIR level, without proving anything:
//!
//! 1. fold the same real 2-turn chain → the `ir2_leaf_wrap` apex;
//! 2. build the apex-verifier circuit (the shrink circuit) at the inner
//!    config — exactly what `apex_shrink::shrink_recursion_input_to_outer`
//!    step (1) does;
//! 3. CENSUS the circuit's op list (Const/Public/Alu-by-kind/Horner-chain
//!    shape/NPO rows) — this attributes each table's height to an apex
//!    feature (19 FRI queries × Merkle depth → poseidon2 rows; ~752 opened
//!    columns × 19 queries → Horner/ALU + recompose rows);
//! 4. extract the outer-config table AIRs + degrees at SEVERAL TablePacking
//!    candidates (the same `get_airs_and_degrees_with_prep` call the shrink
//!    prover uses — these are the REAL degrees the prover would commit, not
//!    a model) and report each candidate's table shapes + a hashing-cost
//!    model (BN254 sponge perms ∝ LDE elements/16 at blowup 64).
//!
//! The builder set below MUST mirror `apex_shrink.rs` step (2) — the
//! poseidon2 / recompose(coeff-off) / expose_claim preprocessor+builder set
//! at D=4. If apex_shrink changes its set, change this too.
//!
//! Run (slow: one real 2-turn fold, ~4min):
//!   cargo test -p dregg-circuit-prove --release --test apex_shrink_trace_anatomy -- --ignored --nocapture

use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::dregg_outer_config::DreggOuterConfig;
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend,
};
use dregg_turn_prover::rotation_witness::mint_rotated_participant_leg;
use p3_air::BaseAir;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_circuit::ops::NpoTypeId;
use p3_circuit::{AluOpKind, Circuit, Op};
use p3_circuit_prover::{
    ConstraintProfile, TablePacking,
    common::{CircuitTableAir, NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep},
    expose_claim_air_builders, expose_claim_preprocessor, poseidon2_air_builders,
    poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
};
use p3_field::extension::BinomialExtensionField;
use p3_recursion::{BatchOnly, build_next_layer_circuit};

const D: usize = 4;
type EF = BinomialExtensionField<P3BabyBear, D>;
/// The outer FRI blowup the shrink is proven at (dregg_outer_config).
const LOG_BLOWUP: usize = 6;
/// BabyBear limbs absorbed per Poseidon2Bn254 permutation by the outer MMCS
/// leaf sponge (8 limbs/rate slot × 2 rate slots).
const LIMBS_PER_PERM: usize = 16;

// ---- the same real fixture as apex_shrink_bn254_tooth.rs ------------------

fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn make_turn(balance: u64, nonce: u32, amount: u64) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell((balance as i64) - (amount as i64), nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0, 7), make_turn(1000 - 7, 1, 7)]
}

// ---- shape extraction ------------------------------------------------------

struct TableShape {
    name: String,
    degree: usize,
    main_width: usize,
    prep_width: usize,
    max_constraint_degree: Option<usize>,
}

/// Mirror of apex_shrink.rs step (2): outer-config table AIRs + degrees at a
/// given packing. Same preprocessor/builder set, same constraint profile.
fn shapes_at(
    circuit: &Circuit<EF>,
    packing: &TablePacking,
) -> (Vec<TableShape>, Vec<(String, usize)>) {
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![
        poseidon2_preprocessor::<P3BabyBear>(),
        recompose_preprocessor::<P3BabyBear>(false),
        expose_claim_preprocessor::<P3BabyBear>(),
    ];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggOuterConfig, D>>> = {
        let mut builders = poseidon2_air_builders::<DreggOuterConfig, D>();
        builders.extend(recompose_air_builders::<DreggOuterConfig, D>(1, false));
        builders.extend(expose_claim_air_builders::<DreggOuterConfig, D>());
        builders
    };
    let (airs_degrees, _prim, npo) = get_airs_and_degrees_with_prep::<DreggOuterConfig, EF, D>(
        circuit,
        packing,
        &preprocessors,
        &air_builders,
        ConstraintProfile::Standard,
    )
    .expect("outer-config table-AIR extraction");

    // Reconstruct Dynamic-table names: builders run in registration order
    // (poseidon2, recompose, expose_claim), each over the SORTED matched op
    // types — the same iteration get_airs_and_degrees_with_prep performs.
    let mut npo_keys: Vec<String> = npo.keys().map(|k| k.as_str().to_string()).collect();
    npo_keys.sort();
    let mut dynamic_names: Vec<String> = Vec::new();
    for prefix in ["poseidon2_perm/", "recompose", "expose_claim"] {
        for k in &npo_keys {
            let matched = if prefix.ends_with('/') {
                k.starts_with(prefix)
            } else {
                k == prefix
            };
            if matched {
                dynamic_names.push(k.clone());
            }
        }
    }

    let npo_prep_lens: Vec<(String, usize)> = {
        let mut v: Vec<(String, usize)> = npo
            .iter()
            .map(|(k, cols)| (k.as_str().to_string(), cols.len()))
            .collect();
        v.sort();
        v
    };

    let mut dyn_i = 0usize;
    let shapes = airs_degrees
        .iter()
        .map(|(air, degree)| {
            let (name, main_width, prep_width, mcd) = match air {
                CircuitTableAir::Const(a) => (
                    "Const".to_string(),
                    BaseAir::<P3BabyBear>::width(a),
                    BaseAir::<P3BabyBear>::preprocessed_width(a),
                    BaseAir::<P3BabyBear>::max_constraint_degree(a),
                ),
                CircuitTableAir::Public(a) => (
                    "Public".to_string(),
                    BaseAir::<P3BabyBear>::width(a),
                    BaseAir::<P3BabyBear>::preprocessed_width(a),
                    BaseAir::<P3BabyBear>::max_constraint_degree(a),
                ),
                CircuitTableAir::Alu(a) => (
                    "Alu".to_string(),
                    BaseAir::<P3BabyBear>::width(a),
                    BaseAir::<P3BabyBear>::preprocessed_width(a),
                    BaseAir::<P3BabyBear>::max_constraint_degree(a),
                ),
                CircuitTableAir::Dynamic(a) => {
                    let name = dynamic_names
                        .get(dyn_i)
                        .cloned()
                        .unwrap_or_else(|| format!("dynamic#{dyn_i}"));
                    dyn_i += 1;
                    (
                        name,
                        BaseAir::<P3BabyBear>::width(a),
                        BaseAir::<P3BabyBear>::preprocessed_width(a),
                        BaseAir::<P3BabyBear>::max_constraint_degree(a),
                    )
                }
            };
            TableShape {
                name,
                degree: *degree,
                main_width,
                prep_width,
                max_constraint_degree: mcd,
            }
        })
        .collect();
    (shapes, npo_prep_lens)
}

/// Hashing-cost MODEL (labelled as such everywhere it is printed): the outer
/// prover's dominant cost is Poseidon2Bn254 permutations. Leaf sponging of a
/// committed matrix ≈ LDE_rows × ceil(width/16) perms; the shared Merkle tree
/// adds ≈ 2 × max_LDE_rows compress perms per commit. Quotient commit ≈
/// rows × D × (max_constraint_degree − 1) extra elements per instance.
fn perm_model(shapes: &[TableShape]) -> (u64, u64, u64) {
    let mut main_perms = 0u64;
    let mut prep_perms = 0u64;
    let mut quotient_perms = 0u64;
    for s in shapes {
        let lde_rows = 1u64 << (s.degree + LOG_BLOWUP);
        main_perms += lde_rows * (s.main_width as u64).div_ceil(LIMBS_PER_PERM as u64);
        if s.prep_width > 0 {
            prep_perms += lde_rows * (s.prep_width as u64).div_ceil(LIMBS_PER_PERM as u64);
        }
        let chunks = s
            .max_constraint_degree
            .unwrap_or(3)
            .saturating_sub(1)
            .max(1) as u64;
        // quotient chunk matrices: D base columns each, `chunks` of them.
        quotient_perms += lde_rows * ((D as u64) * chunks).div_ceil(LIMBS_PER_PERM as u64);
    }
    (main_perms, prep_perms, quotient_perms)
}

#[test]
#[ignore = "SLOW: one real 2-turn fold (~4min) then shape extraction only (no proving); run with --ignored --nocapture"]
fn apex_verifier_air_trace_anatomy() {
    // ---- 1. the real apex --------------------------------------------------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    println!("apex fold time: {:?}", t0.elapsed());

    let inner_config = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let input = whole.root.into_recursion_input::<BatchOnly>();

    // ---- 2. the apex-verifier circuit (shrink circuit) ----------------------
    let t1 = Instant::now();
    let (circuit, _verifier_result) = build_next_layer_circuit::<
        DreggRecursionConfig,
        BatchOnly,
        _,
        D,
    >(&input, &inner_config, &backend)
    .expect("apex-verifier circuit builds");
    println!("circuit build time: {:?}", t1.elapsed());

    // ---- 3. op census --------------------------------------------------------
    let mut n_const = 0u64;
    let mut n_public = 0u64;
    let mut n_hint = 0u64;
    let mut n_npo = 0u64;
    let mut n_add = 0u64;
    let mut n_mul = 0u64;
    let mut n_bool = 0u64;
    let mut n_muladd = 0u64;
    let mut n_horner = 0u64;
    let mut horner_runs = 0u64;
    let mut longest_run = 0u64;
    let mut cur_run = 0u64;
    for op in &circuit.ops {
        let is_horner = matches!(
            op,
            Op::Alu {
                kind: AluOpKind::HornerAcc,
                ..
            }
        );
        if is_horner {
            if cur_run == 0 {
                horner_runs += 1;
            }
            cur_run += 1;
            longest_run = longest_run.max(cur_run);
        } else {
            cur_run = 0;
        }
        match op {
            Op::Const { .. } => n_const += 1,
            Op::Public { .. } => n_public += 1,
            Op::Hint { .. } => n_hint += 1,
            Op::NonPrimitiveOpWithExecutor { .. } => n_npo += 1,
            Op::Alu { kind, .. } => match kind {
                AluOpKind::Add => n_add += 1,
                AluOpKind::Mul => n_mul += 1,
                AluOpKind::BoolCheck => n_bool += 1,
                AluOpKind::MulAdd => n_muladd += 1,
                AluOpKind::HornerAcc => n_horner += 1,
            },
        }
    }
    println!("\n=== APEX-VERIFIER CIRCUIT OP CENSUS ===");
    println!("witness_count      : {}", circuit.witness_count);
    println!("public_flat_len    : {}", circuit.public_flat_len);
    println!("private_flat_len   : {}", circuit.private_flat_len);
    println!("Const ops          : {n_const}");
    println!("Public ops         : {n_public}");
    println!("Hint ops           : {n_hint}");
    println!("NonPrimitive ops   : {n_npo}");
    println!(
        "Alu ops            : {} (Add {n_add} / Mul {n_mul} / Bool {n_bool} / MulAdd {n_muladd} / HornerAcc {n_horner})",
        n_add + n_mul + n_bool + n_muladd + n_horner
    );
    println!(
        "Horner chains      : {horner_runs} maximal runs, longest {longest_run}, avg {:.1}",
        if horner_runs > 0 {
            n_horner as f64 / horner_runs as f64
        } else {
            0.0
        }
    );

    // ---- 4. table shapes at packing candidates ------------------------------
    // Baseline = ProveNextLayerParams::default().table_packing (public 1, alu 4,
    // horner 2, npo 1). Candidates vary alu lanes / horner pack / npo lanes.
    let candidates: Vec<(&str, TablePacking)> = vec![
        ("BASELINE p1/a4/h2", TablePacking::new(1, 4)),
        ("a8/h2", TablePacking::new(1, 8)),
        ("a4/h4", TablePacking::new(1, 4).with_horner_pack_k(4)),
        ("a8/h4", TablePacking::new(1, 8).with_horner_pack_k(4)),
        ("a8/h8", TablePacking::new(1, 8).with_horner_pack_k(8)),
        (
            "a8/h4/rec4",
            TablePacking::new(1, 8)
                .with_horner_pack_k(4)
                .with_npo_lanes(NpoTypeId::recompose(), 4),
        ),
        (
            "a8/h8/rec8",
            TablePacking::new(1, 8)
                .with_horner_pack_k(8)
                .with_npo_lanes(NpoTypeId::recompose(), 8),
        ),
        (
            "a16/h8/rec8",
            TablePacking::new(1, 16)
                .with_horner_pack_k(8)
                .with_npo_lanes(NpoTypeId::recompose(), 8),
        ),
    ];

    let mut baseline_total: Option<u64> = None;
    for (name, packing) in &candidates {
        let (shapes, npo_lens) = shapes_at(&circuit, packing);
        println!("\n=== PACKING {name} ===");
        println!(
            "{:<34} {:>6} {:>8} {:>8} {:>6}",
            "table", "log2", "main_w", "prep_w", "maxdeg"
        );
        for s in &shapes {
            println!(
                "{:<34} {:>6} {:>8} {:>8} {:>6}",
                s.name,
                s.degree,
                s.main_width,
                s.prep_width,
                s.max_constraint_degree
                    .map(|d| d.to_string())
                    .unwrap_or_else(|| "?".into()),
            );
        }
        let degrees: Vec<usize> = shapes.iter().map(|s| s.degree).collect();
        let (main_perms, prep_perms, quot_perms) = perm_model(&shapes);
        let total = main_perms + prep_perms + quot_perms;
        println!("degree_bits: {degrees:?}");
        println!(
            "MODEL perms @blowup64 (leaf-sponge only): main {main_perms} + prep {prep_perms} + quotient(est) {quot_perms} = {total}"
        );
        if baseline_total.is_none() {
            baseline_total = Some(total);
            println!("(baseline reference)");
            println!("NPO preprocessed lens: {npo_lens:?}");
        } else if let Some(base) = baseline_total {
            println!("MODEL vs baseline: {:.2}x", total as f64 / base as f64);
        }
    }
}
