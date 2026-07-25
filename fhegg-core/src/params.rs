//! The deployed BFV parameter set — relocated here (from the GPU-coupled `additive.rs`) so the threshold
//! party ops can live in this wasm-clean crate without a cyclic dep back into fhegg-fhe.

use std::sync::Arc;

use fhe::bfv::BfvParameters;

/// The deployed degree-4096, 128-bit-security BFV parameters for `plaintext_nbits` plaintext modulus bits.
/// The single source of truth both the fold/aggregation lane and the threshold committee build against.
pub fn pick_params(plaintext_nbits: usize) -> Arc<BfvParameters> {
    BfvParameters::default_parameters_128(plaintext_nbits)
        .expect("128-bit BFV params")
        .nth(2)
        .expect("degree-4096 parameter set")
}
