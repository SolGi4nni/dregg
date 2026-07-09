//! PSEUDORANDOMNESS — statistical SMOKE test (`Pseudorandom` in the Lean
//! framework). Without `sk`, the VRF output must look uniform.
//!
//! This is a smoke test, NOT a security proof: the actual game (indistinguishability
//! from uniform) is the assumed `Pseudorandom` predicate in `Dregg2/Crypto/VRF.lean`,
//! whose floor is the underlying hash/PRG. Here we check the OUTPUT DISTRIBUTION has
//! no gross bias — a necessary sanity condition. Thresholds are lenient and the
//! sample is drawn from a fixed seed, so the test is deterministic (no flakiness).

use crypto_xmvrf::hash::prg_xof;
use crypto_xmvrf::keygen_from_seed;

/// Collect the VRF outputs across every epoch of several keys into one byte pool.
fn collect_output_bytes() -> Vec<u8> {
    let height = 8u8; // 256 outputs per key
    let mut pool = Vec::new();
    for k in 0u8..16 {
        let (_pk, sk) = keygen_from_seed(&[k; 32], height);
        for epoch in 0..(1u64 << height) {
            let (y, _proof) = sk.eval(epoch).unwrap();
            pool.extend_from_slice(&y);
        }
    }
    pool // 16 keys * 256 epochs * 32 bytes = 131072 bytes
}

/// MONOBIT: the fraction of 1-bits over the whole output pool must be ~0.5.
#[test]
fn monobit_balance() {
    let pool = collect_output_bytes();
    let total_bits = pool.len() * 8;
    let ones: usize = pool.iter().map(|b| b.count_ones() as usize).sum();
    let frac = ones as f64 / total_bits as f64;
    assert!(
        (frac - 0.5).abs() < 0.01,
        "bit balance {frac:.5} deviates too far from 0.5 over {total_bits} bits"
    );
}

/// BYTE CHI-SQUARE: byte values should be ~uniform over 0..256. We use a lenient
/// bound well inside the tail for a pool this size (df = 255).
#[test]
fn byte_uniformity_chi_square() {
    let pool = collect_output_bytes();
    let n = pool.len() as f64;
    let expected = n / 256.0;
    let mut counts = [0u64; 256];
    for &b in &pool {
        counts[b as usize] += 1;
    }
    let chi2: f64 = counts
        .iter()
        .map(|&c| {
            let d = c as f64 - expected;
            d * d / expected
        })
        .sum();
    // df = 255: mean 255, sd ~22.6. A random blake3 stream lands well under 400;
    // a grossly biased generator blows past it. Lenient one-sided sanity bound.
    assert!(
        chi2 < 400.0,
        "byte chi-square {chi2:.1} too high (df=255) — output not uniform enough"
    );
}

/// DISTINCTNESS: across many keys and epochs, outputs must (essentially) never
/// collide — a keyed-PRF sanity check. Any collision in this pool is a red flag.
#[test]
fn outputs_are_distinct_across_keys_and_epochs() {
    use std::collections::HashSet;
    let height = 7u8; // 128 epochs
    let mut seen: HashSet<[u8; 32]> = HashSet::new();
    let mut count = 0usize;
    for k in 0u8..24 {
        let (_pk, sk) = keygen_from_seed(&[k.wrapping_mul(37).wrapping_add(1); 32], height);
        for epoch in 0..(1u64 << height) {
            let (y, _p) = sk.eval(epoch).unwrap();
            assert!(seen.insert(y), "unexpected output collision");
            count += 1;
        }
    }
    assert_eq!(count, 24 * 128);
}

/// The output looks uniform vs. a reference PRG stream: compares the monobit of
/// the VRF pool to an independent blake3 XOF stream of equal length — both must be
/// close to 0.5 and to each other. A directional sanity check that the VRF output
/// is not detectably less uniform than raw PRG bytes.
#[test]
fn vrf_output_matches_prg_reference_balance() {
    let pool = collect_output_bytes();
    let reference = prg_xof(&[0x5Au8; 32], b"reference-stream", pool.len());

    let frac = |bytes: &[u8]| {
        let ones: usize = bytes.iter().map(|b| b.count_ones() as usize).sum();
        ones as f64 / (bytes.len() * 8) as f64
    };
    let f_vrf = frac(&pool);
    let f_ref = frac(&reference);
    assert!(
        (f_vrf - f_ref).abs() < 0.01,
        "VRF bit balance {f_vrf:.5} diverges from PRG reference {f_ref:.5}"
    );
}
