//! Independent proof-byte retention and tamper-disposition audit.
//!
//! Compile against the already-built exact dregg-circuit rlib.  This is not a
//! timing harness.  It retains five verified postcard proofs per fixture and
//! distinguishes producer refusal from rejection by the consumer verifier.

use std::fs;
use std::path::{Path, PathBuf};

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const CASES: [(&str, &str); 8] = [
    ("admission", "source"),
    ("admission", "optimized"),
    ("upgrade", "source"),
    ("upgrade", "optimized"),
    ("clearance", "source"),
    ("clearance", "optimized"),
    ("strand", "source"),
    ("strand", "optimized"),
];

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn parse_csv(path: &Path) -> Vec<u32> {
    let text = read(path);
    let body = text.strip_suffix('\n').expect("canonical trailing newline");
    body.split(',')
        .map(|x| x.parse().expect("canonical u32"))
        .collect()
}

fn digest(path: &Path) -> String {
    blake3::hash(&fs::read(path).expect("fixture bytes"))
        .to_hex()
        .to_string()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let fixtures = PathBuf::from(args.next().expect("fixture directory"));
    let proofs = PathBuf::from(args.next().expect("proof output directory"));
    fs::create_dir_all(&proofs).expect("create proof output directory");
    println!("workload,variant,kind,sample,bytes,blake3,disposition");
    for (workload, variant) in CASES {
        let stem = fixtures.join(format!("{workload}-{variant}"));
        let descriptor_path = stem.with_extension("descriptor.json");
        let trace_path = stem.with_extension("trace.csv");
        let public_path = stem.with_extension("public.csv");
        let truth_path = stem.with_extension("truth.csv");
        let descriptor_text = read(&descriptor_path);
        let descriptor = parse_vm_descriptor2(&descriptor_text).expect("exact descriptor parses");
        let trace: Vec<BabyBear> = parse_csv(&trace_path)
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let public: Vec<BabyBear> = parse_csv(&public_path)
            .into_iter()
            .map(BabyBear::new)
            .collect();
        let truth = parse_csv(&truth_path);
        for (kind, path) in [
            ("descriptor", &descriptor_path),
            ("trace", &trace_path),
            ("public", &public_path),
            ("truth", &truth_path),
        ] {
            println!(
                "{workload},{variant},fixture-{kind},0,{},{},pinned",
                fs::metadata(path).unwrap().len(),
                digest(path)
            );
        }
        for sample in 0..5 {
            let proof = prove_vm_descriptor2(
                &descriptor,
                std::slice::from_ref(&trace),
                &public,
                &MemBoundaryWitness::default(),
                &[],
            )
            .expect("honest proof produced");
            verify_vm_descriptor2(&descriptor, &proof, &public)
                .expect("consumer verifies honest proof");
            let bytes = postcard::to_allocvec(&proof).expect("postcard proof bytes");
            let hash = blake3::hash(&bytes).to_hex().to_string();
            let path = proofs.join(format!("{workload}-{variant}-{sample}.postcard"));
            fs::write(path, &bytes).expect("retain proof bytes");
            println!(
                "{workload},{variant},honest-proof,{sample},{},{hash},consumer_verified",
                bytes.len()
            );
        }
        let mut tampered = public.clone();
        tampered[0] = if truth[0] == 1 {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
        let disposition = match prove_vm_descriptor2(
            &descriptor,
            std::slice::from_ref(&trace),
            &tampered,
            &MemBoundaryWitness::default(),
            &[],
        ) {
            Err(_) => "producer_refused",
            Ok(proof) => match verify_vm_descriptor2(&descriptor, &proof, &tampered) {
                Err(_) => "consumer_verifier_rejected",
                Ok(()) => "UNSOUND_ACCEPT",
            },
        };
        println!("{workload},{variant},public-input-tamper,0,0,none,{disposition}");
    }
}
