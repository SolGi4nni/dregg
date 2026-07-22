//! Fixed-descriptor, varied-accepting-assignment timing and proof-byte sweep.

use std::fs;
use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::time::Instant;

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};

const REPEATS: usize = 10;
const CASES: [(&str, &[&str]); 3] = [
    (
        "admission",
        &["expiry-none", "expiry-timed", "expiry-both-abstract"],
    ),
    ("branch", &["left", "right", "both"]),
    (
        "strand",
        &[
            "seed",
            "vouch",
            "bond",
            "seed-vouch",
            "seed-bond",
            "vouch-bond",
            "all",
        ],
    ),
];

fn read(path: &Path) -> String {
    fs::read_to_string(path).unwrap()
}

fn parse_csv(path: &Path) -> Vec<BabyBear> {
    let text = read(path);
    text.strip_suffix('\n')
        .unwrap()
        .split(',')
        .map(|x| BabyBear::new(x.parse::<u32>().unwrap()))
        .collect()
}

struct Loaded {
    descriptor: dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: Vec<BabyBear>,
    public: Vec<BabyBear>,
}

fn load(root: &Path, shape: &str, assignment: &str, variant: &str) -> Loaded {
    let stem = root.join(format!("{shape}-{assignment}-{variant}"));
    Loaded {
        descriptor: parse_vm_descriptor2(&read(&stem.with_extension("descriptor.json"))).unwrap(),
        trace: parse_csv(&stem.with_extension("trace.csv")),
        public: parse_csv(&stem.with_extension("public.csv")),
    }
}

fn prove(
    loaded: &Loaded,
) -> dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig> {
    prove_vm_descriptor2(
        &loaded.descriptor,
        std::slice::from_ref(&loaded.trace),
        &loaded.public,
        &MemBoundaryWitness::default(),
        &[],
    )
    .unwrap()
}

fn main() {
    let mut args = std::env::args().skip(1);
    let inputs = PathBuf::from(args.next().expect("input directory"));
    let proofs = PathBuf::from(args.next().expect("proof output directory"));
    fs::create_dir_all(&proofs).unwrap();
    println!(
        "META,repeats={REPEATS},order=alternating,verification=outside_timed_prove,proof_encoding=postcard"
    );
    for (shape, assignments) in CASES {
        for assignment in assignments {
            let loaded = [
                load(&inputs, shape, assignment, "source"),
                load(&inputs, shape, assignment, "optimized"),
            ];
            for round in 0..REPEATS {
                let order = if round % 2 == 0 { [0, 1] } else { [1, 0] };
                for index in order {
                    let variant = if index == 0 { "source" } else { "optimized" };
                    let start = Instant::now();
                    let proof = prove(&loaded[index]);
                    let elapsed = start.elapsed().as_nanos();
                    verify_vm_descriptor2(&loaded[index].descriptor, &proof, &loaded[index].public)
                        .unwrap();
                    let bytes = postcard::to_allocvec(&proof).unwrap();
                    let hash = blake3::hash(&bytes).to_hex().to_string();
                    let path =
                        proofs.join(format!("{shape}-{assignment}-{variant}-{round}.postcard"));
                    fs::write(path, &bytes).unwrap();
                    println!(
                        "SWEEP,{shape},{assignment},{variant},{round},{elapsed},{},{hash}",
                        bytes.len()
                    );
                    black_box(proof);
                }
            }
        }
    }
}
