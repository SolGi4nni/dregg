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
//!   - beyond the Lean spec: the production-shaped
//!     discrete-GAUSSIAN flooding variant
//!     (CDT sampler, tail-cut `⌈τσ⌉`)                    → [`threshold::DiscreteGaussian`]
//!     / [`threshold::hermine_sign_gaussian`]; its hiding (TV shrinking in
//!     `σ`) is witnessed EMPIRICALLY, not Lean-pinned — the Lean `Smudging`
//!     proof covers the uniform+TV leg only
//!   - the `ShortNorm` carrier (shortness of `z`,
//!     `z − z'`)                                         → [`threshold::signature_norm`]
//!     / [`threshold::acceptance_bound`]
//! * beyond the Lean spec: the RACCOON 2-round MASKING +
//!   COMMIT-THEN-REVEAL ceremony (the real scheme's
//!   concurrency mechanism)                              → [`threshold::hermine_sign_raccoon`]
//!   / [`threshold::RaccoonSignSession`]; one-time flooded masks, each
//!   `w_i = A·y_i` bound by a blake3 hash commitment BEFORE any reveal, then
//!   the same verify relation `A·z = w + c•t` over `w = Σ w_i` — the
//!   concurrency security is the Hint-MLWE straight-line argument
//!   (formalized in the metatheory separately)
//! * beyond the Lean spec: the NETWORK-CEREMONY shape ([`ceremony`]) — the
//!   DKG and the Raccoon 2-round signing driven as MESSAGE-PASSING protocols
//!   over a transport abstraction ([`ceremony::Channel`]), with serde-carried
//!   round messages and the commit-then-reveal boundary enforced by the
//!   transport's round barrier; reference [`ceremony::LocalNetwork`] only —
//!   a real async network transport is the next engineering layer
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
//! * **keygen** — the real-key path is now the dealerless Pedersen-style DKG
//!   ([`dkg::HermineDkg`]): every member deals its OWN short secret with
//!   Feldman-style commitments (`A·coeff` broadcasts), received shares are
//!   VERIFIED against the broadcasts (a cheating dealer is detected and
//!   named), final shares sum to a t-of-n sharing of `s = Σᵢ sᵢ` that no
//!   party ever holds. The trusted [`threshold::HermineTestDealer`] remains
//!   ONLY for known-secret algebra tests. The DKG itself is still a
//!   REFERENCE: message-shaped over a transport abstraction
//!   ([`ceremony::run_dkg_ceremony`]) but with an in-memory synchronous
//!   reference transport only, detection without complaint-round
//!   arbitration, no rushing-adversary bias fix (Gennaro et al.), reference
//!   PRNG — see [`dkg`]'s and [`ceremony`]'s boundary docs;
//! * **concurrency defense = Raccoon commit-then-reveal (reference)** — the
//!   concurrent/rushing-adversary defense is the Raccoon-aligned 2-round
//!   ceremony ([`threshold::hermine_sign_raccoon`]): Round 1 broadcasts only
//!   hash commitments `cm_i = H("dregg-raccoon-commit" ‖ i ‖ w_i)`; Round 2
//!   reveals are verified against them (equivocation is detected and NAMED),
//!   then `w = Σ w_i`, a domain-separated blake3 challenge, and the
//!   unchanged threshold algebra. The concurrency security argument is
//!   STRAIGHT-LINE under Hint-MLWE (the metatheory's leg, not this crate's);
//!   the ceremony is MESSAGE-SHAPED over a transport abstraction
//!   ([`ceremony`]) but the reference transport is in-memory and synchronous
//!   (no real network, timeouts, or retransmission), non-constant-time,
//!   pre-audit. The unbound [`threshold::hermine_sign`]
//!   remains single-ceremony-only (its shared-commitment fork is the
//!   extractor tests' hypothesis);
//! * **reference PRNG, non-constant-time samplers** — noise-flooding now
//!   comes in BOTH variants: the uniform+TV one the Lean `Smudging` spec
//!   proves (masks uniform over `[-M/2, M/2)`) AND the production-shaped
//!   discrete-GAUSSIAN one (CDT sampler over a `⌈τσ⌉` tail,
//!   [`threshold::hermine_sign_gaussian`]) with the TV-vs-σ hiding trade
//!   witnessed empirically. But both run over splitmix64 — NOT a CSPRNG —
//!   and the Gaussian CDT lookup is a value-dependent binary search — NOT
//!   constant-time. A CSPRNG + constant-time (data-independent) sampling +
//!   external audit are the remaining production steps on this leg;
//! * **toy challenge hash** — non-cryptographic; it does squeeze a SHORT
//!   ternary challenge (`‖c‖∞ ≤ 1`, which the smudging shift bound needs),
//!   but not the deployed fixed-weight unit-difference challenge set;
//! * **combined-signature flooding only** — per-signer partials ride
//!   full-range Lagrange coefficients; the real threshold scheme's
//!   per-party masking/shortness story is out of scope;
//! * **realistic-ward, not production, parameters** — `n = 256` (the production dimension) with the
//!   Dilithium prime `q = 8380417` (NTT-friendly, real-modulus arithmetic;
//!   the hiding/shortness gap is now real headroom, not a demonstration
//!   sliver), but production Hermine needs `n ≥ 256` and vetted `k×ℓ`/σ
//!   from the parameter-search literature;
//! * **not constant-time**, and no zeroization of secrets.
//!
//! The production signer needs the DKG's deployment machinery (a REAL
//! network transport behind the [`ceremony::Channel`] seam — encrypted
//! private channels, timeouts, retransmission — complaint-round arbitration,
//! the bias fix; the PROTOCOL is already message-shaped in [`ceremony`]),
//! plus the Hint-MLWE straight-line concurrency formalization (the
//! metatheory's leg), a CSPRNG,
//! constant-time arithmetic and sampling, full-size parameters, and external
//! audit. This crate's value is different: every identity the
//! Lean proofs establish is witnessed here on concrete `R_q` numbers —
//! including the Smudging key-hiding bound as an empirical total-variation
//! measurement, in both its uniform (Lean-pinned) and discrete-Gaussian
//! (production-shaped) forms — so the spec and the reference cannot
//! silently drift apart.

pub mod ceremony;
pub mod dkg;
pub mod linalg;
pub mod ring;
pub mod threshold;

pub use ceremony::{
    run_dkg_ceremony, run_sign_ceremony, CeremonyError, Channel, ChannelError, DkgAckMsg,
    DkgCeremonyParams, DkgDealingMsg, DkgPartyOutput, LocalChannel, LocalNetwork,
    RaccoonResponseMsg,
};
pub use dkg::{dkg_deal, verify_dkg_share, DkgDealing, DkgError, DkgShareMsg, HermineDkg};
pub use linalg::{Matrix, PolyVec};
pub use ring::{Poly, N, Q};
pub use threshold::{
    acceptance_bound, extract_preimage, extracted_relation, hermine_sign, hermine_sign_gaussian,
    hermine_sign_raccoon, hermine_sign_with_mask_width, lagrange_reconstruct, partial_response,
    raccoon_challenge, raccoon_commitment, sample_gaussian_mask, sample_wide_mask, signature_norm,
    verify_hermine, verify_hermine_raccoon, DiscreteGaussian, HermineShare, HermineSignature,
    HermineTestDealer, RaccoonCommitMsg, RaccoonError, RaccoonRevealMsg, RaccoonSignSession,
    RaccoonSigner, GAUSSIAN_TAIL_CUT, MASK_WIDTH_WIDE, SECRET_ETA,
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
