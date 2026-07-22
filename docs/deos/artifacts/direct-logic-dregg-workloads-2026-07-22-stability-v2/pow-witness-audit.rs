//! Extract the public FRI query-grinding witness from retained postcard proofs.

use std::fs;
use std::path::PathBuf;

use dregg_circuit::descriptor_ir2::{DreggStarkConfig, Ir2BatchProof};
use p3_field::PrimeField32;

fn main() {
    let root = PathBuf::from(std::env::args().nth(1).expect("proof directory"));
    println!("file,query_pow_witness");
    let mut paths: Vec<_> = fs::read_dir(root)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "postcard")
        })
        .collect();
    paths.sort();
    for path in paths {
        let bytes = fs::read(&path).unwrap();
        let proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(&bytes).unwrap();
        println!(
            "{},{}",
            path.file_name().unwrap().to_string_lossy(),
            proof.opening_proof.query_pow_witness.as_canonical_u32()
        );
    }
}
