//! Reproducible, stage-separated benchmark for the checked direct-logic front end.
//!
//! Run in release mode and retain stdout as the raw artifact:
//!
//! ```text
//! cargo run -p dregg-circuit --release --bin direct_logic_live_benchmark
//! ```
//!
//! The benchmark deliberately reports proof generation separately from
//! verification and never interprets either measurement as blockchain finality.

use std::hint::black_box;
use std::time::{Duration, Instant};

use dregg_circuit::descriptor_ir2::{
    IR2_EXT_DEGREE, IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN, IR2_FRI_MAX_LOG_ARITY,
    IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS, MemBoundaryWitness, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::direct_logic_frontend::{
    BoolExpr, CompileLimits, Formula, InputDecl, LogicProgram, LogicType, LogicValue, Term,
    compile_logic_program, evaluate_logic_program,
};

#[derive(Clone)]
struct Workload {
    name: String,
    program: LogicProgram,
    inputs: Vec<LogicValue>,
}

fn bool_equality() -> Workload {
    Workload {
        name: "bool-eq".into(),
        program: LogicProgram {
            inputs: vec![InputDecl {
                name: "x".into(),
                ty: LogicType::Bool,
            }],
            formula: Formula::Equal(
                Term::Input(0),
                Term::Constant {
                    ty: LogicType::Bool,
                    value: 1,
                },
            ),
        },
        inputs: vec![LogicValue::Bool(true)],
    }
}

fn enum_equality(cardinality: usize) -> Workload {
    let ty = LogicType::Finite { cardinality };
    Workload {
        name: format!("enum-eq-{cardinality}"),
        program: LogicProgram {
            inputs: vec![InputDecl {
                name: "x".into(),
                ty: ty.clone(),
            }],
            formula: Formula::Equal(
                Term::Input(0),
                Term::Constant {
                    ty: ty.clone(),
                    value: cardinality - 1,
                },
            ),
        },
        inputs: vec![LogicValue::Finite(cardinality - 1)],
    }
}

fn quantified_tautology(cardinality: usize) -> Workload {
    let ty = LogicType::Finite { cardinality };
    let equality = Formula::Equal(Term::Input(0), Term::Bound(0));
    Workload {
        name: format!("forall-tautology-{cardinality}"),
        program: LogicProgram {
            inputs: vec![InputDecl {
                name: "x".into(),
                ty: ty.clone(),
            }],
            // This is intentionally not folded by the compiler. It exercises
            // deterministic quantifier expansion and a large exact Boolean
            // relation while remaining true for every canonical input.
            formula: Formula::ForAll {
                binder: ty.clone(),
                body: Box::new(Formula::Or(
                    Box::new(equality.clone()),
                    Box::new(Formula::Not(Box::new(equality))),
                )),
            },
        },
        inputs: vec![LogicValue::Finite(cardinality / 2)],
    }
}

fn expr_nodes(expr: &BoolExpr) -> usize {
    match expr {
        BoolExpr::Atom(_) | BoolExpr::Constant(_) => 1,
        BoolExpr::Not(value) => 1 + expr_nodes(value),
        BoolExpr::And(left, right) | BoolExpr::Or(left, right) => {
            1 + expr_nodes(left) + expr_nodes(right)
        }
    }
}

fn env_samples(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .filter(|count: &usize| *count > 0)
        .unwrap_or(default)
}

fn elapsed_ns<T>(mut f: impl FnMut() -> T) -> (T, u128) {
    let start = Instant::now();
    let value = f();
    (value, start.elapsed().as_nanos())
}

fn sample_ns<T>(samples: usize, mut f: impl FnMut() -> T) -> Vec<u128> {
    (0..samples)
        .map(|_| {
            let start = Instant::now();
            black_box(f());
            start.elapsed().as_nanos()
        })
        .collect()
}

fn print_samples(workload: &str, stage: &str, samples: &[u128]) {
    for (sample, elapsed_ns) in samples.iter().enumerate() {
        println!("SAMPLE,{workload},{stage},{sample},{elapsed_ns}");
    }
}

fn main() {
    let compile_samples = env_samples("DREGG_LOGIC_BENCH_COMPILE_SAMPLES", 100);
    let witness_samples = env_samples("DREGG_LOGIC_BENCH_WITNESS_SAMPLES", 1_000);
    let prove_samples = env_samples("DREGG_LOGIC_BENCH_PROVE_SAMPLES", 12);
    let verify_samples = env_samples("DREGG_LOGIC_BENCH_VERIFY_SAMPLES", 30);
    let warmups = env_samples("DREGG_LOGIC_BENCH_WARMUPS", 3);
    let limits = CompileLimits::default();
    let workloads = [
        bool_equality(),
        enum_equality(4),
        enum_equality(16),
        enum_equality(64),
        quantified_tautology(4),
        quantified_tautology(8),
        quantified_tautology(16),
    ];

    println!(
        "META,version=1,profile=release,warmups={warmups},compile_samples={compile_samples},\
         witness_samples={witness_samples},prove_samples={prove_samples},\
         verify_samples={verify_samples},proof_encoding=postcard,field=babybear,\
         ext_degree={IR2_EXT_DEGREE},fri_log_blowup={IR2_FRI_LOG_BLOWUP},\
         fri_log_final_poly_len={IR2_FRI_LOG_FINAL_POLY_LEN},\
         fri_max_log_arity={IR2_FRI_MAX_LOG_ARITY},fri_queries={IR2_FRI_NUM_QUERIES},\
         fri_query_pow_bits={IR2_FRI_QUERY_POW_BITS},trace_rows=1"
    );

    for workload in workloads {
        assert!(
            evaluate_logic_program(&workload.program, &workload.inputs)
                .expect("reference evaluation")
        );

        for _ in 0..warmups {
            black_box(
                compile_logic_program(&workload.program, &limits).expect("warm compile must pass"),
            );
        }
        let compile_times = sample_ns(compile_samples, || {
            compile_logic_program(&workload.program, &limits).expect("compile must pass")
        });

        let artifact = compile_logic_program(&workload.program, &limits).expect("compile artifact");
        for _ in 0..warmups {
            black_box(
                artifact
                    .one_row_trace(&workload.inputs)
                    .expect("warm witness must pass"),
            );
        }
        let witness_times = sample_ns(witness_samples, || {
            artifact
                .one_row_trace(&workload.inputs)
                .expect("witness must pass")
        });
        let trace = artifact
            .one_row_trace(&workload.inputs)
            .expect("benchmark witness");

        for _ in 0..warmups {
            let warm_proof = prove_vm_descriptor2(
                artifact.descriptor(),
                &trace,
                &[],
                &MemBoundaryWitness::default(),
                &[],
            )
            .expect("warm proof must pass");
            verify_vm_descriptor2(artifact.descriptor(), &warm_proof, &[])
                .expect("warm proof must verify");
        }

        let mut last_proof = None;
        let mut prove_times = Vec::with_capacity(prove_samples);
        for _ in 0..prove_samples {
            let (proof, elapsed) = elapsed_ns(|| {
                prove_vm_descriptor2(
                    artifact.descriptor(),
                    &trace,
                    &[],
                    &MemBoundaryWitness::default(),
                    &[],
                )
                .expect("proof must pass")
            });
            prove_times.push(elapsed);
            last_proof = Some(proof);
        }
        let proof = last_proof.expect("positive proof sample count");
        verify_vm_descriptor2(artifact.descriptor(), &proof, &[])
            .expect("captured proof must verify");
        let proof_bytes =
            postcard::to_allocvec(&proof).expect("serialize proof with live wire codec");

        for _ in 0..warmups {
            verify_vm_descriptor2(artifact.descriptor(), &proof, &[])
                .expect("warm verify must pass");
        }
        let verify_times = sample_ns(verify_samples, || {
            verify_vm_descriptor2(artifact.descriptor(), &proof, &[]).expect("verify must pass")
        });

        println!(
            "WORKLOAD,{},{},{},{},{},{},{}",
            workload.name,
            artifact.logical_atom_count(),
            artifact.descriptor().trace_width,
            artifact.descriptor().constraints.len(),
            expr_nodes(artifact.source_relation()),
            artifact.descriptor_bytes().len(),
            proof_bytes.len(),
        );
        let degree_bits = proof
            .degree_bits
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(":");
        println!("PROOF_SHAPE,{},degree_bits={degree_bits}", workload.name);
        print_samples(&workload.name, "compile", &compile_times);
        print_samples(&workload.name, "witness", &witness_times);
        print_samples(&workload.name, "prove", &prove_times);
        print_samples(&workload.name, "verify", &verify_times);

        // Avoid releasing substantial proof buffers in the timed sections.
        black_box(Duration::from_nanos(
            u64::try_from(prove_times.iter().sum::<u128>()).unwrap_or(u64::MAX),
        ));
    }
}
