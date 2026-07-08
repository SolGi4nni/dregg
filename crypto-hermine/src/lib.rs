//! # crypto-hermine — a spec-faithful REFERENCE implementation of the Hermine
//! lattice threshold signature (IACR ePrint 2026/419, the Raccoon-based
//! FROST-analog), pinned to the verified Lean spec.
//!
//! ## Provenance — the Lean spec this crate matches, symbol for symbol
//!
//! * `metatheory/Dregg2/Crypto/HermineThreshold.lean`
//!   - `verify A t w c z := A z = w + c • t`             → [`verify`]
//!   - `raccoon_sig_verifies` (`z = y + c·s` verifies)   → the single-signer
//!     case of the threshold tests
//!   - `hermine_cert_verifies_under_group_key`
//!     (`s = Σ λ_i•s_i`, `z_i = y_i + c•(λ_i•s_i)`,
//!     `z = Σ z_i`, `w = A(Σ y_i)`, `t = A·s`)           → [`threshold::hermine_sign`]
//!   - `hermine_share_is_valid_under_key_share`          → [`threshold::partial_response`]
//!     / [`threshold::HermineShare::key_share`]
//! * `metatheory/Dregg2/Crypto/HermineExtractor.lean`
//!   - `hermine_special_soundness_extracts_relation`
//!     (`A(z − z') = (c − c')•t` from two accepting
//!     transcripts sharing a commitment)                 → [`threshold::extracted_relation`]
//!   - `extractPreimage c c' z z' = (c−c')⁻¹•(z−z')`     → [`threshold::extract_preimage`]
//! * `metatheory/Dregg2/Crypto/Smudging.lean` — noise-flooding, the KEY-HIDING leg
//!   - `unif S` over a wide interval `[-M/2, M/2)`       → [`threshold::sample_wide_mask`]
//!   - `smudge_bound` (statistical distance `≤ B/M`
//!     between the flooded response distributions
//!     under two secrets, `B ≥ ‖c·Δs‖∞`)                 → the empirical TV
//!     key-hiding test in [`threshold`] (wide mask hides; narrow mask leaks)
//!   - the `ShortNorm` carrier (shortness of `z`,
//!     `z − z'`)                                         → [`threshold::signature_norm`]
//!     / [`threshold::acceptance_bound`]
//!
//! The Lean spec is stated over an abstract `R`-linear map `A : M →ₗ[R] N`.
//! This reference instantiates `R = R_q = ℤ_q[X]/(Xⁿ+1)` ([`ring`]),
//! `M = R_q^ℓ`, `N = R_q^k`, and `A` a `k×ℓ` matrix over `R_q` ([`linalg`]) —
//! the module structure the deployed scheme actually uses. The instantiation's
//! linearity (the Lean hypothesis) is itself tested, not assumed.
//!
//! ## Production boundary — what this crate is NOT
//!
//! This is the exact executable the verified Lean spec pins, for tests and
//! differentials. It is NOT deployment-grade and must never be wired into
//! live signing:
//!
//! * **trusted dealer** — keygen centralizes the group secret (no DKG);
//! * **no binding factors** — single-ceremony only; concurrent-session
//!   (Drijvers/ROS-style) attacks are out of model;
//! * **UNIFORM noise-flooding over a reference PRNG** — the key-hiding
//!   mechanism is PRESENT (masks uniform over the wide `[-M/2, M/2)`,
//!   matching the Lean `Smudging` spec's `unif`/`smudge_bound`, with
//!   shortness accounting on `z` and `z − z'`), but it is the uniform+TV
//!   variant over splitmix64: production Raccoon/Hermine uses
//!   discrete-GAUSSIAN flooding with a Rényi-divergence bound for tighter
//!   parameters, a CSPRNG, and constant-time samplers;
//! * **toy challenge hash** — non-cryptographic; it does squeeze a SHORT
//!   ternary challenge (`‖c‖∞ ≤ 1`, which the smudging shift bound needs),
//!   but not the deployed fixed-weight unit-difference challenge set;
//! * **combined-signature flooding only** — per-signer partials ride
//!   full-range Lagrange coefficients; the real threshold scheme's
//!   per-party masking/shortness story is out of scope;
//! * **toy parameters** — `n = 8`, `q = 3329`, small `k×ℓ`; real Hermine
//!   parameters are orders of magnitude larger (the hiding/shortness gap
//!   here is demonstration-sized, not security-sized);
//! * **not constant-time**, and no zeroization of secrets.
//!
//! The production signer needs a DKG, binding factors, Gaussian flooding
//! with a CSPRNG, real parameters, constant-time arithmetic, and external
//! audit. This crate's value is different: every identity the Lean proofs
//! establish is witnessed here on concrete `R_q` numbers — including,
//! now, the Smudging key-hiding bound as an empirical total-variation
//! measurement — so the spec and the reference cannot silently drift apart.

pub mod linalg;
pub mod ring;
pub mod threshold;

pub use linalg::{Matrix, PolyVec};
pub use ring::{Poly, N, Q};
pub use threshold::{
    acceptance_bound, extract_preimage, extracted_relation, hermine_sign,
    hermine_sign_with_mask_width, partial_response, sample_wide_mask, signature_norm,
    verify_hermine, HermineShare, HermineSignature, HermineTestDealer, MASK_WIDTH_WIDE, SECRET_ETA,
};

/// Lattice verification — the Lean `HermineThreshold.verify`, symbol for
/// symbol: a signature `z` verifies against public key `t = A·s`, commitment
/// `w`, and challenge `c` iff `A·z = w + c•t`.
pub fn verify(a: &Matrix, t: &PolyVec, w: &PolyVec, c: &Poly, z: &PolyVec) -> bool {
    a.mul_vec(z) == w.add(&t.scale(c))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn poly(seed: u64) -> Poly {
        let mut coeffs = [0u64; N];
        let mut s = seed;
        for c in coeffs.iter_mut() {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            *c = (s >> 17) % Q;
        }
        Poly { coeffs }
    }

    fn vec3(seed: u64) -> PolyVec {
        PolyVec(vec![poly(seed), poly(seed + 1), poly(seed + 2)])
    }

    #[test]
    fn raccoon_sig_verifies_single_signer() {
        // The Lean raccoon_sig_verifies: for ANY s, y, c —
        // verify A (A s) (A y) c (y + c • s).
        let a = Matrix::from_fn(2, 3, |r, c| poly(1000 + (r * 3 + c) as u64));
        for (si, yi, ci) in [(1u64, 2u64, 3u64), (40, 50, 60), (700, 800, 900)] {
            let s = vec3(si);
            let y = vec3(yi * 31);
            let c = poly(ci * 97);
            let z = y.add(&s.scale(&c));
            assert!(verify(&a, &a.mul_vec(&s), &a.mul_vec(&y), &c, &z));
            // And a perturbed response fails: the relation has teeth.
            let mut bad = z.clone();
            bad.0[0] = bad.0[0].add(&Poly::constant(1));
            assert!(!verify(&a, &a.mul_vec(&s), &a.mul_vec(&y), &c, &bad));
        }
    }
}
