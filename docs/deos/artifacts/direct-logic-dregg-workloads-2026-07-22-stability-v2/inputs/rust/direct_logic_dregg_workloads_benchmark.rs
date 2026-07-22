//! Paired live BatchSTARK benchmark for the Lean-certified DREGG workloads.
//!
//! The descriptor bytes and canonical one-row traces are emitted by
//! `tools/direct-logic-dregg-benchmark/Emit.lean`.  This harness never rebuilds
//! the formulas or witnesses in Rust: it byte-pins, parses, checks, proves, and
//! verifies those emitted artifacts directly.

use std::hint::black_box;
use std::time::Instant;

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, IR2_EXT_DEGREE, IR2_FRI_LOG_BLOWUP, IR2_FRI_LOG_FINAL_POLY_LEN,
    IR2_FRI_MAX_LOG_ARITY, IR2_FRI_NUM_QUERIES, IR2_FRI_QUERY_POW_BITS, MemBoundaryWitness,
    VmConstraint2, WindowExpr, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const FIXTURE_ROOT: &str = "../../../tools/direct-logic-dregg-benchmark/generated";

#[derive(Clone, Copy)]
struct Fixture {
    workload: &'static str,
    variant: &'static str,
    descriptor_json: &'static str,
    trace_csv: &'static str,
    public_csv: &'static str,
    truth_csv: &'static str,
    expected_blake3: &'static str,
    atoms: usize,
    trace_width: usize,
    constraints: usize,
    multiplications: usize,
    auxiliaries: usize,
}

macro_rules! fixture {
    ($workload:literal, $variant:literal, $hash:literal, $atoms:literal,
     $width:literal, $constraints:literal, $multiplications:literal, $aux:literal) => {
        Fixture {
            workload: $workload,
            variant: $variant,
            descriptor_json: include_str!(concat!(
                "../../../tools/direct-logic-dregg-benchmark/generated/",
                $workload,
                "-",
                $variant,
                ".descriptor.json"
            )),
            trace_csv: include_str!(concat!(
                "../../../tools/direct-logic-dregg-benchmark/generated/",
                $workload,
                "-",
                $variant,
                ".trace.csv"
            )),
            public_csv: include_str!(concat!(
                "../../../tools/direct-logic-dregg-benchmark/generated/",
                $workload,
                "-",
                $variant,
                ".public.csv"
            )),
            truth_csv: include_str!(concat!(
                "../../../tools/direct-logic-dregg-benchmark/generated/",
                $workload,
                "-",
                $variant,
                ".truth.csv"
            )),
            expected_blake3: $hash,
            atoms: $atoms,
            trace_width: $width,
            constraints: $constraints,
            multiplications: $multiplications,
            auxiliaries: $aux,
        }
    };
}

// Hashes are filled from `--print-pins` after running the Lean emitter.  They
// bind the Rust benchmark to the reviewed byte images, not merely to any JSON
// object that happens to parse.
const FIXTURES: [Fixture; 8] = [
    fixture!(
        "admission",
        "source",
        "7306ad678e59093b0bf785075984ef5083f9f5d94b386ac23f4309172d4113af",
        12,
        77,
        121,
        108,
        65
    ),
    fixture!(
        "admission",
        "optimized",
        "5ca61f08c5eb58b89daa75c08ab5e426d1a6b227534e7c9be3d6b6d08fe81a63",
        12,
        47,
        71,
        58,
        35
    ),
    fixture!(
        "upgrade",
        "source",
        "78349d6d32967532081347c0425e1314e217e6856816b84cc91d57eef86efdad",
        4,
        21,
        33,
        28,
        17
    ),
    fixture!(
        "upgrade",
        "optimized",
        "256630f65ba021f12fdd90ab78416623f68044523c0bea5be8009d5d1312cfa8",
        4,
        15,
        23,
        18,
        11
    ),
    fixture!(
        "clearance",
        "source",
        "78349d6d32967532081347c0425e1314e217e6856816b84cc91d57eef86efdad",
        4,
        21,
        33,
        28,
        17
    ),
    fixture!(
        "clearance",
        "optimized",
        "256630f65ba021f12fdd90ab78416623f68044523c0bea5be8009d5d1312cfa8",
        4,
        15,
        23,
        18,
        11
    ),
    fixture!(
        "strand",
        "source",
        "7921a03108a473f4fc87c61ba19972fe7ce1af19b3f7b814126d3d63850c7309",
        3,
        11,
        17,
        13,
        8
    ),
    fixture!(
        "strand",
        "optimized",
        "7921a03108a473f4fc87c61ba19972fe7ce1af19b3f7b814126d3d63850c7309",
        3,
        11,
        17,
        13,
        8
    ),
];

struct LoadedFixture {
    spec: Fixture,
    descriptor: EffectVmDescriptor2,
    trace: Vec<BabyBear>,
    public: Vec<BabyBear>,
    truth: Vec<u32>,
    actual_blake3: String,
}

fn parse_csv_u32(label: &str, csv: &str) -> Result<Vec<u32>, String> {
    let body = csv
        .strip_suffix('\n')
        .ok_or_else(|| format!("{label}: missing canonical trailing newline"))?;
    if body.is_empty() {
        return Ok(Vec::new());
    }
    body.split(',')
        .enumerate()
        .map(|(index, value)| {
            value
                .parse::<u32>()
                .map_err(|error| format!("{label}[{index}]={value:?}: {error}"))
        })
        .collect()
}

fn nonconstant_multiplications(expression: &WindowExpr) -> usize {
    match expression {
        WindowExpr::Loc(_) | WindowExpr::Nxt(_) | WindowExpr::Const(_) => 0,
        WindowExpr::Add(left, right) => {
            nonconstant_multiplications(left) + nonconstant_multiplications(right)
        }
        WindowExpr::Mul(left, right) => {
            nonconstant_multiplications(left)
                + nonconstant_multiplications(right)
                + usize::from(
                    !matches!(&**left, WindowExpr::Const(_))
                        && !matches!(&**right, WindowExpr::Const(_)),
                )
        }
    }
}

fn descriptor_multiplications(descriptor: &EffectVmDescriptor2) -> Result<usize, String> {
    descriptor
        .constraints
        .iter()
        .map(|constraint| match constraint {
            VmConstraint2::Base(dregg_circuit::lean_descriptor_air::VmConstraint::PiBinding {
                ..
            }) => Ok(0),
            VmConstraint2::WindowGate(gate) => Ok(nonconstant_multiplications(&gate.body)),
            other => Err(format!(
                "unexpected constraint in direct-logic fixture: {other:?}"
            )),
        })
        .sum()
}

fn load_fixture(spec: Fixture, require_pin: bool) -> Result<LoadedFixture, String> {
    let actual_blake3 = blake3::hash(spec.descriptor_json.as_bytes())
        .to_hex()
        .to_string();
    if require_pin && actual_blake3 != spec.expected_blake3 {
        return Err(format!(
            "{}-{} byte pin mismatch: expected {}, got {}",
            spec.workload, spec.variant, spec.expected_blake3, actual_blake3
        ));
    }
    let descriptor = parse_vm_descriptor2(spec.descriptor_json)?;
    let trace_values = parse_csv_u32("trace", spec.trace_csv)?;
    let public_values = parse_csv_u32("public", spec.public_csv)?;
    let truth = parse_csv_u32("truth", spec.truth_csv)?;
    if descriptor.trace_width != spec.trace_width
        || descriptor.public_input_count != spec.atoms
        || descriptor.constraints.len() != spec.constraints
        || trace_values.len() != spec.trace_width
        || public_values.len() != spec.atoms
        || truth.len() != spec.atoms
        || descriptor_multiplications(&descriptor)? != spec.multiplications
        || descriptor.trace_width - spec.atoms != spec.auxiliaries
    {
        return Err(format!(
            "{}-{} emitted layout/count mismatch",
            spec.workload, spec.variant
        ));
    }
    if truth.iter().any(|value| *value > 1)
        || public_values
            .iter()
            .zip(&truth)
            .any(|(residual, bit)| *residual != 1 - *bit)
    {
        return Err(format!(
            "{}-{} noncanonical truth/public encoding",
            spec.workload, spec.variant
        ));
    }
    Ok(LoadedFixture {
        spec,
        descriptor,
        trace: trace_values.into_iter().map(BabyBear::new).collect(),
        public: public_values.into_iter().map(BabyBear::new).collect(),
        truth,
        actual_blake3,
    })
}

fn env_samples(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .filter(|count: &usize| *count > 0)
        .unwrap_or(default)
}

fn timed<T>(f: impl FnOnce() -> T) -> (T, u128) {
    let start = Instant::now();
    let value = f();
    (value, start.elapsed().as_nanos())
}

fn prove(
    fixture: &LoadedFixture,
) -> dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig> {
    prove_vm_descriptor2(
        &fixture.descriptor,
        std::slice::from_ref(&fixture.trace),
        &fixture.public,
        &MemBoundaryWitness::default(),
        &[],
    )
    .unwrap_or_else(|error| {
        panic!(
            "{}-{} honest Lean trace refused: {error}",
            fixture.spec.workload, fixture.spec.variant
        )
    })
}

fn paired_indices(round: usize) -> [usize; 2] {
    if round.is_multiple_of(2) {
        [0, 1]
    } else {
        [1, 0]
    }
}

fn public_tamper_rejected(fixture: &LoadedFixture) -> bool {
    let mut tampered_public = fixture.public.clone();
    tampered_public[0] = if fixture.truth[0] == 1 {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    match prove_vm_descriptor2(
        &fixture.descriptor,
        std::slice::from_ref(&fixture.trace),
        &tampered_public,
        &MemBoundaryWitness::default(),
        &[],
    ) {
        Err(_) => true,
        Ok(proof) => verify_vm_descriptor2(&fixture.descriptor, &proof, &tampered_public).is_err(),
    }
}

fn print_pins() {
    for spec in FIXTURES {
        let loaded = load_fixture(spec, false).expect("Lean fixture must parse and match counts");
        println!(
            "{}-{},{}",
            spec.workload, spec.variant, loaded.actual_blake3
        );
    }
}

fn main() {
    if std::env::args().any(|arg| arg == "--print-pins") {
        print_pins();
        return;
    }

    let prove_samples = env_samples("DREGG_DLOGIC_PROVE_SAMPLES", 25);
    let verify_samples = env_samples("DREGG_DLOGIC_VERIFY_SAMPLES", 75);
    let warmups = env_samples("DREGG_DLOGIC_WARMUPS", 5);
    assert!(
        prove_samples >= 20,
        "capture requires at least 20 prove samples"
    );
    assert!(
        verify_samples >= 50,
        "capture requires at least 50 verify samples"
    );

    println!(
        "META,version=1,fixture_root={FIXTURE_ROOT},profile=release,warmups={warmups},\
         prove_samples={prove_samples},verify_samples={verify_samples},pair_order=alternating,\
         proof_encoding=postcard,release_prover_self_verify=false,field=babybear,\
         ext_degree={IR2_EXT_DEGREE},\
         fri_log_blowup={IR2_FRI_LOG_BLOWUP},\
         fri_log_final_poly_len={IR2_FRI_LOG_FINAL_POLY_LEN},\
         fri_max_log_arity={IR2_FRI_MAX_LOG_ARITY},fri_queries={IR2_FRI_NUM_QUERIES},\
         fri_query_pow_bits={IR2_FRI_QUERY_POW_BITS},trace_rows=1"
    );

    for pair in FIXTURES.chunks_exact(2) {
        let loaded = [
            load_fixture(pair[0], true).expect("source fixture must pass byte/count gates"),
            load_fixture(pair[1], true).expect("optimized fixture must pass byte/count gates"),
        ];
        assert_eq!(loaded[0].spec.workload, loaded[1].spec.workload);
        assert_eq!(
            loaded[0].public, loaded[1].public,
            "public assignment drift"
        );
        assert_eq!(loaded[0].truth, loaded[1].truth, "truth assignment drift");
        for fixture in &loaded {
            assert!(
                public_tamper_rejected(fixture),
                "{}-{} accepted a public-input tamper",
                fixture.spec.workload,
                fixture.spec.variant
            );
            println!(
                "TAMPER,{},{},public_input_0,verifier_rejected",
                fixture.spec.workload, fixture.spec.variant
            );
        }

        for round in 0..warmups {
            for index in paired_indices(round) {
                let proof = prove(&loaded[index]);
                verify_vm_descriptor2(&loaded[index].descriptor, &proof, &loaded[index].public)
                    .expect("warm proof must verify");
                black_box(proof);
            }
        }

        let mut proofs = [None, None];
        for round in 0..prove_samples {
            for index in paired_indices(round) {
                let (proof, elapsed_ns) = timed(|| prove(&loaded[index]));
                verify_vm_descriptor2(&loaded[index].descriptor, &proof, &loaded[index].public)
                    .expect("every measured proof must verify");
                println!(
                    "SAMPLE,{},{},prove,{round},{elapsed_ns}",
                    loaded[index].spec.workload, loaded[index].spec.variant
                );
                proofs[index] = Some(proof);
            }
        }

        for round in 0..verify_samples {
            for index in paired_indices(round) {
                let proof = proofs[index].as_ref().expect("positive prove sample count");
                let (_, elapsed_ns) = timed(|| {
                    verify_vm_descriptor2(
                        &loaded[index].descriptor,
                        black_box(proof),
                        &loaded[index].public,
                    )
                    .expect("retained proof must verify")
                });
                println!(
                    "SAMPLE,{},{},verify,{round},{elapsed_ns}",
                    loaded[index].spec.workload, loaded[index].spec.variant
                );
            }
        }

        for index in 0..2 {
            let proof = proofs[index].as_ref().expect("positive prove sample count");
            let proof_bytes = postcard::to_allocvec(proof).expect("postcard proof encoding");
            let degree_bits = proof
                .degree_bits
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(":");
            println!(
                "WORKLOAD,{},{},{},{},{},{},{},{},{},{},{},degree_bits={}",
                loaded[index].spec.workload,
                loaded[index].spec.variant,
                loaded[index].spec.atoms,
                loaded[index].spec.trace_width,
                loaded[index].descriptor.public_input_count,
                loaded[index].spec.constraints,
                loaded[index].spec.multiplications,
                loaded[index].spec.auxiliaries,
                loaded[index].spec.descriptor_json.len(),
                loaded[index].actual_blake3,
                proof_bytes.len(),
                degree_bits,
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean_emitted_fixtures_are_pinned_parseable_and_exactly_counted() {
        for spec in FIXTURES {
            load_fixture(spec, true).unwrap();
        }
    }

    #[test]
    fn lean_canonical_traces_prove_and_public_tamper_is_refused() {
        for spec in FIXTURES {
            let fixture = load_fixture(spec, true).unwrap();
            let proof = prove(&fixture);
            verify_vm_descriptor2(&fixture.descriptor, &proof, &fixture.public).unwrap();

            assert!(
                public_tamper_rejected(&fixture),
                "{}-{} accepted a public-input tamper",
                spec.workload,
                spec.variant
            );
        }
    }
}
