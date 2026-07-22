//! Consumer-verifier timing across every accepting assignment and descriptor endpoint.

use std::fs;
use std::hint::black_box;
use std::path::{Path, PathBuf};
use std::time::Instant;

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, parse_vm_descriptor2,
    verify_vm_descriptor2,
};

const WARMUPS: usize = 20;
const REPEATS: usize = 200;
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

struct Loaded {
    descriptor: EffectVmDescriptor2,
    public: Vec<BabyBear>,
    proof: Ir2BatchProof<DreggStarkConfig>,
}

fn parse_public(path: &Path) -> Vec<BabyBear> {
    let text = fs::read_to_string(path).unwrap();
    text.strip_suffix('\n')
        .unwrap()
        .split(',')
        .map(|value| BabyBear::new(value.parse().unwrap()))
        .collect()
}

fn load(inputs: &Path, proofs: &Path, shape: &str, assignment: &str, variant: &str) -> Loaded {
    let stem = inputs.join(format!("{shape}-{assignment}-{variant}"));
    let descriptor =
        parse_vm_descriptor2(&fs::read_to_string(stem.with_extension("descriptor.json")).unwrap())
            .unwrap();
    let public = parse_public(&stem.with_extension("public.csv"));
    let proof_bytes =
        fs::read(proofs.join(format!("{shape}-{assignment}-{variant}-0.postcard"))).unwrap();
    let proof = postcard::from_bytes(&proof_bytes).unwrap();
    verify_vm_descriptor2(&descriptor, &proof, &public).unwrap();
    Loaded {
        descriptor,
        public,
        proof,
    }
}

fn verify(loaded: &Loaded) {
    verify_vm_descriptor2(
        black_box(&loaded.descriptor),
        black_box(&loaded.proof),
        black_box(&loaded.public),
    )
    .unwrap();
}

fn main() {
    let mut args = std::env::args().skip(1);
    let session = args.next().expect("session label");
    let inputs = PathBuf::from(args.next().expect("input directory"));
    let proofs = PathBuf::from(args.next().expect("proof directory"));
    println!(
        "META,session={session},warmups={WARMUPS},repeats={REPEATS},order=alternating,consumer_verifier=true"
    );
    for (shape, assignments) in CASES {
        for assignment in assignments {
            let loaded = [
                load(&inputs, &proofs, shape, assignment, "source"),
                load(&inputs, &proofs, shape, assignment, "optimized"),
            ];
            for round in 0..WARMUPS {
                let order = if round % 2 == 0 { [0, 1] } else { [1, 0] };
                for index in order {
                    verify(&loaded[index]);
                }
            }
            for round in 0..REPEATS {
                let order = if round % 2 == 0 { [0, 1] } else { [1, 0] };
                for index in order {
                    let variant = if index == 0 { "source" } else { "optimized" };
                    let start = Instant::now();
                    verify(&loaded[index]);
                    let elapsed = start.elapsed().as_nanos();
                    println!(
                        "VERIFY_SWEEP,{session},{shape},{assignment},{variant},{round},{elapsed}"
                    );
                }
            }
        }
    }
}
