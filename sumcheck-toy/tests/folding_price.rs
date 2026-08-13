//! # THE OTHER HALF OF THE EXCHANGE RATE, MEASURED
//!
//! `zkml-research/paper/scripts/boundary_exchange_rate.py` prices one committed base felt
//! at ~3,120 field multiplications (lb=4) and prices VIRTUALIZING one at
//! `(d-1) * k * 10 = 40` mult-equiv per value per sumcheck layer. **That `10` is a fudge
//! constant, not a measurement**, and the whole threshold rule ("virtualize while the layer
//! count is below the exchange rate") hangs off it.
//!
//! This measures the virtualize side directly: the wall-clock of a complete
//! `p3-sumcheck` fold over `2^n` values, divided by `2^n`, giving **nanoseconds per value
//! per layer** at degree 2 on the deployed challenger. Its companion —
//! `dregg-circuit/tests/poseidon2_virtualization_measure.rs` — gives nanoseconds per
//! committed felt from the same box, so the ratio is a measured exchange rate rather than a
//! modelled one.
//!
//! ## ⚠ WHAT THIS CANNOT SEE
//!
//! `p3-sumcheck`'s `ProductPolynomial` is **degree 2 only**. A Poseidon2 S-box layer is
//! degree `alpha + 1 = 8`, and a degree-`D` round message costs `D+1` evaluations rather
//! than 3. So the degree scaling in the note that consumes this number is **modelled**, and
//! only the `d = 2` point is measured. Saying otherwise would be quoting the flattering
//! member of a pair.
//!
//! There is also no polynomial commitment here (see the crate docblock), so this prices the
//! FOLD and nothing downstream of it.

use std::time::Instant;

use p3_multilinear_util::poly::Poly;
use sumcheck_toy::{
    F, Packing, challenger, fixture_poly, product_sum, prove_product, verify_product,
};

const REPS: usize = 5;

fn measure(n: usize, packing: Packing) -> (f64, f64) {
    let f: Poly<F> = fixture_poly(n, 0xF00D);
    let g: Poly<F> = fixture_poly(n, 0xBEEF);

    let mut best = f64::MAX;
    for _ in 0..REPS {
        let mut chal = challenger();
        let t0 = Instant::now();
        let (claimed, proof) = prove_product(&f, &g, 0, packing, &mut chal);
        best = best.min(t0.elapsed().as_secs_f64());

        // ⚠ The clock is only worth reading if the protocol actually ran and was accepted.
        // A fold that silently produced a degenerate transcript would time beautifully.
        assert_eq!(claimed, product_sum(&f, &g));
        let mut v = challenger();
        verify_product(&g, claimed, &proof, 0, &mut v).expect("the measured fold must verify");
        assert_eq!(
            proof.rounds.num_rounds(),
            n,
            "a fold with fewer rounds is a different measurement"
        );
    }

    let values = (1usize << n) as f64;
    (best * 1e3, best * 1e9 / values)
}

/// ⚠ `--ignored`: a measurement, not a gate.
/// `cargo test -p sumcheck-toy --release --test folding_price -- --ignored --nocapture`
#[test]
#[ignore = "measurement"]
fn folding_nanoseconds_per_value_per_layer() {
    println!("== SUMCHECK FOLDING PRICE (degree 2, BabyBear -> Ext4, deployed challenger) ==");
    println!("   min of {REPS}; one COMPLETE n-round fold over 2^n values = one 'layer'");
    println!(
        "   {:>3} {:>10} {:>12} {:>12}",
        "n", "values", "ms/fold", "ns/value/layer"
    );
    for n in [12usize, 14, 16, 18, 20] {
        let (ms, ns_per) = measure(n, Packing::Packed);
        println!(
            "   {:>3} {:>10} {:>12.3} {:>12.3}",
            n,
            1usize << n,
            ms,
            ns_per
        );
    }
    println!("   (scalar packing, for the SIMD delta)");
    for n in [16usize, 20] {
        let (ms, ns_per) = measure(n, Packing::Scalar);
        println!(
            "   {:>3} {:>10} {:>12.3} {:>12.3}",
            n,
            1usize << n,
            ms,
            ns_per
        );
    }
}
