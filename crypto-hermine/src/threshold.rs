//! Trusted-dealer Shamir keygen over `R_q` and the single-ceremony threshold
//! signing helper — the Lean `hermine_cert_verifies_under_group_key` algebra,
//! executably. Structural mirror of `federation/src/frost.rs`'s
//! `FrostTestDealer` / `frost_sign`, over a module instead of a prime-order
//! group.
//!
//! # Noise-flooding — the key-hiding mechanism (`Dregg2.Crypto.Smudging`)
//!
//! A lattice signature `z = y + c·s` leaks `s` unless the mask distribution
//! smudges the secret-dependent shift out. This reference implements BOTH
//! flooding variants:
//!
//! * **UNIFORM** — the variant the Lean `Smudging` module proves sound: each
//!   mask coefficient uniform over the WIDE centered range `[-M/2, M/2)`
//!   ([`sample_wide_mask`], `M =` [`MASK_WIDTH_WIDE`] by default), so by
//!   `smudge_bound` the statistical distance between response distributions
//!   under two secrets is `≤ ‖c·Δs‖∞ / M` per coefficient — driven small by
//!   making `M` dwarf the shift.
//! * **DISCRETE GAUSSIAN** — the variant production Raccoon/Hermine deploys
//!   (tighter parameters via Rényi-divergence accounting): each mask
//!   coefficient from a centered discrete Gaussian of width `σ`
//!   ([`DiscreteGaussian`] / [`sample_gaussian_mask`], signing path
//!   [`hermine_sign_gaussian`]). The Lean spec pins the uniform+TV leg only;
//!   the Gaussian leg's hiding is witnessed EMPIRICALLY here (the TV between
//!   z-distributions under two secrets shrinks as `σ` grows — the Gaussian
//!   analogue of `smudge_bound`, `TV ≲ ‖c·Δs‖∞ / (σ√(2π))` per coefficient).
//!
//! Either way the algebra (`z_i = y_i + c·(λ_i·s_i)`, `z = Σ z_i`,
//! `w = A(Σ y_i)`) is unchanged: flooding changes only the mask
//! DISTRIBUTION. The flooded mask also gives the signature its SHORTNESS:
//! [`signature_norm`] and [`acceptance_bound`] carry the norm side (the
//! Lean `Lattice.ShortNorm` carrier, now concrete).
//!
//! # Production-signing boundary (read before even THINKING about wiring)
//!
//! Everything here is fit for tests and differentials against the Lean spec,
//! and for NOTHING else:
//! * the dealer transiently knows the group secret (no DKG);
//! * both flooding samplers run over a REFERENCE PRNG (splitmix64) — NOT a
//!   CSPRNG — and the Gaussian CDT sampler is table-lookup-by-binary-search,
//!   NOT constant-time (its timing depends on the sampled value); those two
//!   plus external audit are the remaining production steps;
//! * the challenge is a toy non-cryptographic hash — it does squeeze a SHORT
//!   (ternary, `‖c‖∞ ≤ 1`) challenge so the smudging shift bound is real,
//!   but it is not the deployed fixed-weight unit-difference challenge set;
//! * only the COMBINED signature `z` is short/flooded — per-signer partials
//!   ride Lagrange coefficients that are full-range in `ℤ_q` (the real
//!   threshold scheme's per-party masking story is out of scope);
//! * no RFC-style per-signer binding factors (concurrent-session attacks
//!   apply), no constant-time arithmetic, toy parameters.

use crate::linalg::{Matrix, PolyVec};
use crate::ring::{inv_mod_q, Poly, N, Q};
use crate::verify;

// =============================================================================
// Toy deterministic sampling (splitmix64) — reference-only, NOT cryptographic
// =============================================================================

/// splitmix64 step — the toy PRNG behind deterministic dealing and masking.
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

/// A uniform-ish (mod-biased; irrelevant for a reference) element of `R_q`.
fn sample_poly(state: &mut u64) -> Poly {
    let mut coeffs = [0u64; N];
    for c in coeffs.iter_mut() {
        *c = splitmix64(state) % Q;
    }
    Poly { coeffs }
}

/// A vector of `len` sampled ring elements.
fn sample_vec(state: &mut u64, len: usize) -> PolyVec {
    PolyVec((0..len).map(|_| sample_poly(state)).collect())
}

/// A SHORT ring element with coefficients uniform in `{-η, …, η}` (centered,
/// stored mod `q`) — the MLWE-style short secret sampler. Toy PRNG.
fn sample_short_poly(state: &mut u64, eta: u64) -> Poly {
    let mut coeffs = [0u64; N];
    for c in coeffs.iter_mut() {
        let v = (splitmix64(state) % (2 * eta + 1)) as i64 - eta as i64;
        *c = v.rem_euclid(Q as i64) as u64;
    }
    Poly { coeffs }
}

/// A short vector: `len` components from [`sample_short_poly`].
fn sample_short_vec(state: &mut u64, len: usize, eta: u64) -> PolyVec {
    PolyVec((0..len).map(|_| sample_short_poly(state, eta)).collect())
}

// =============================================================================
// Noise-flooding mask sampling — the Smudging.lean mechanism
// =============================================================================

/// The default flooding width `M` used by [`hermine_sign`].
///
/// Chosen for the current parameters (`N = 64`, `q = 8380417`) so that BOTH
/// sides of the trade hold at threshold `t = 3`:
/// * **hiding** — the smudging leakage `‖c·s‖∞ / M ≤ 128/2²¹ ≈ 0.006%` per
///   coefficient (ternary `c`, secret `‖s‖∞ ≤` [`SECRET_ETA`], so the shift
///   is `≤ N·1·η = 128`);
/// * **shortness** — the combined honest signature stays wrap-free and
///   genuinely short: `t·(M/2) + 128 = 3145856 < ⌊q/2⌋ = 4190208`, so the
///   [`acceptance_bound`] has teeth.
///
/// Production parameter sets widen this gap further still (larger `n`,
/// Gaussian flooding with Rényi accounting); this reference now leaves real
/// headroom rather than the old demonstration-sized `16/1024` sliver.
pub const MASK_WIDTH_WIDE: u64 = 1 << 21; // 2097152

/// The short-secret coefficient bound `η`: [`HermineTestDealer::deal`]
/// samples the group secret with `‖s‖∞ ≤ η` (centered), the MLWE shape.
pub const SECRET_ETA: u64 = 2;

/// Sample one noise-flooding mask element: each coefficient UNIFORM over the
/// wide centered range `[-m/2, m/2)`, stored mod `q` — the `unif S` of the
/// Lean `Smudging` spec with `S` an `m`-element interval.
///
/// REFERENCE PRNG ONLY: splitmix64 with a `% m` reduction (the mod bias is
/// irrelevant at reference scale). Production flooding needs a CSPRNG and a
/// constant-time sampler; this sampler's job is to make the DISTRIBUTION
/// right so the smudging bound is testable.
pub fn sample_wide_mask(state: &mut u64, m: u64) -> Poly {
    debug_assert!(m >= 2 && m.is_multiple_of(2) && m <= Q);
    let mut coeffs = [0u64; N];
    for c in coeffs.iter_mut() {
        let v = (splitmix64(state) % m) as i64 - (m / 2) as i64;
        *c = v.rem_euclid(Q as i64) as u64;
    }
    Poly { coeffs }
}

/// A flooding mask vector: `len` components from [`sample_wide_mask`].
fn sample_wide_mask_vec(state: &mut u64, len: usize, m: u64) -> PolyVec {
    PolyVec((0..len).map(|_| sample_wide_mask(state, m)).collect())
}

/// The Gaussian tail-cut multiplier τ: the CDT support is `[-⌈τσ⌉, ⌈τσ⌉]`.
///
/// The truncated mass is `≤ 2·exp(-τ²/2) = 2·exp(-50) ≈ 4·10⁻²²` — below
/// f64 resolution, so the table IS the distribution as far as any consumer
/// of this reference can observe.
pub const GAUSSIAN_TAIL_CUT: f64 = 10.0;

/// A centered discrete Gaussian sampler over ℤ, width `σ`, by CDT
/// (cumulative distribution table) — the production-shaped flooding noise
/// (Raccoon/Hermine deploy Gaussian flooding for its tighter
/// Rényi-divergence parameter accounting).
///
/// **Method.** `P[X = k] ∝ exp(-k²/(2σ²))` for `k ∈ [-T, T]`,
/// `T = ⌈τσ⌉` with `τ =` [`GAUSSIAN_TAIL_CUT`] (tail-cut mass `≈ 4e-22`,
/// documented there). [`DiscreteGaussian::new`] normalizes the cumulative
/// table once in f64; [`DiscreteGaussian::sample`] draws a 53-bit uniform
/// from splitmix64 and binary-searches the table. Building the table once
/// per ceremony (not per coefficient) is what keeps the empirical TV tests
/// cheap.
///
/// **Reference boundary.** splitmix64 is NOT a CSPRNG, the binary search is
/// NOT constant-time (timing depends on the sampled value), and f64
/// probabilities carry ≈2⁻⁵³ rounding — production needs a CSPRNG-driven
/// constant-time sampler with fixed-point tables (and audit). Those are the
/// LAST production steps; the distribution itself is right, which is what
/// the reference needs.
pub struct DiscreteGaussian {
    /// The Gaussian width σ.
    sigma: f64,
    /// Tail bound `T = ⌈τσ⌉`: samples lie in `[-T, T]`.
    tail: i64,
    /// `cdt[i] = P[X ≤ i - T]`, monotone, `cdt[2T] = 1`.
    cdt: Vec<f64>,
}

impl DiscreteGaussian {
    /// Build the CDT for width `sigma`. `None` if `sigma` is not strictly
    /// positive and finite, or the tail `⌈τσ⌉` reaches `⌊q/2⌋` (a sample
    /// could then alias under centered reduction mod `q`, breaking the norm
    /// accounting).
    pub fn new(sigma: f64) -> Option<Self> {
        if !sigma.is_finite() || sigma <= 0.0 {
            return None;
        }
        let tail = (GAUSSIAN_TAIL_CUT * sigma).ceil() as i64;
        if tail >= (Q / 2) as i64 {
            return None;
        }
        let mut cdt: Vec<f64> = Vec::with_capacity((2 * tail + 1) as usize);
        let mut acc = 0.0f64;
        for k in -tail..=tail {
            acc += (-(k as f64) * (k as f64) / (2.0 * sigma * sigma)).exp();
            cdt.push(acc);
        }
        let total = acc;
        for p in &mut cdt {
            *p /= total;
        }
        Some(Self { sigma, tail, cdt })
    }

    /// The width σ this sampler was built for.
    pub fn sigma(&self) -> f64 {
        self.sigma
    }

    /// The tail bound `T = ⌈τσ⌉`: every sample satisfies `|X| ≤ T`.
    pub fn tail_bound(&self) -> i64 {
        self.tail
    }

    /// Draw one discrete-Gaussian integer: inverse-CDF by binary search on a
    /// 53-bit splitmix64 uniform. NOT constant-time (see the type doc).
    pub fn sample(&self, state: &mut u64) -> i64 {
        let u = (splitmix64(state) >> 11) as f64 / (1u64 << 53) as f64;
        let idx = self.cdt.partition_point(|&p| p <= u);
        idx.min(self.cdt.len() - 1) as i64 - self.tail
    }
}

/// Sample one Gaussian noise-flooding mask element: each coefficient from
/// the centered discrete Gaussian `gauss`, stored mod `q` — the Gaussian
/// counterpart of [`sample_wide_mask`]. Takes the prebuilt sampler (not a
/// raw σ) so the CDT is built once per ceremony, not once per coefficient.
pub fn sample_gaussian_mask(state: &mut u64, gauss: &DiscreteGaussian) -> Poly {
    let mut coeffs = [0u64; N];
    for c in coeffs.iter_mut() {
        *c = gauss.sample(state).rem_euclid(Q as i64) as u64;
    }
    Poly { coeffs }
}

/// A Gaussian flooding mask vector: `len` components from
/// [`sample_gaussian_mask`].
fn sample_gaussian_mask_vec(state: &mut u64, len: usize, gauss: &DiscreteGaussian) -> PolyVec {
    PolyVec(
        (0..len)
            .map(|_| sample_gaussian_mask(state, gauss))
            .collect(),
    )
}

/// The toy Fiat–Shamir challenge `c = H(w ‖ t ‖ message)`, squeezed into the
/// SHORT ternary set `{-1, 0, 1}^N` (stored mod `q`), so `‖c‖∞ ≤ 1`.
///
/// Domain-separated FNV-1a absorb, splitmix64 squeeze. NON-cryptographic:
/// its only job in the reference is to be a deterministic function of the
/// commitment, the public key, and the message (so honest verification and
/// the two-message forking test are both exact). The SHORTNESS, though, is
/// load-bearing: the smudging shift `‖c·λs‖∞` is only bounded because the
/// challenge is — the deployed scheme's short challenge set, minus its
/// fixed weight and unit-difference structure.
fn challenge(w: &PolyVec, group_key: &PolyVec, message: &[u8]) -> Poly {
    let mut h: u64 = 0xcbf29ce484222325;
    let mut absorb = |byte: u64| {
        h ^= byte;
        h = h.wrapping_mul(0x100000001b3);
    };
    absorb(w.len() as u64);
    for p in &w.0 {
        for &c in &p.coeffs {
            absorb(c);
        }
    }
    absorb(group_key.len() as u64);
    for p in &group_key.0 {
        for &c in &p.coeffs {
            absorb(c);
        }
    }
    absorb(message.len() as u64);
    for &b in message {
        absorb(b as u64);
    }
    let mut state = h;
    sample_short_poly(&mut state, 1)
}

// =============================================================================
// Trusted-dealer Shamir keygen over R_q
// =============================================================================

/// One member's Shamir share of the group secret, dealt by
/// [`HermineTestDealer`] — the Lean `shares i : M`.
#[derive(Clone)]
pub struct HermineShare {
    /// 1-based Shamir evaluation index (x-coordinate; 0 is the group secret).
    pub index: u64,
    /// The share vector `f(index) ∈ R_q^ℓ`.
    share: PolyVec,
}

impl HermineShare {
    /// This member's share verification key `A·(λ_i·s_i)` for a given signing
    /// subset — the key share the Lean
    /// `hermine_share_is_valid_under_key_share` verifies partials against
    /// (the basis of non-interactive identifiable abort).
    pub fn key_share(&self, a: &Matrix, parts: &[u64]) -> PolyVec {
        let lam = Poly::constant(lagrange_at_zero(self.index, parts));
        a.mul_vec(&self.share.scale(&lam))
    }
}

/// Trusted-dealer Shamir keygen over `R_q^ℓ`, and the sampled public matrix.
///
/// The dealer transiently knows the group secret — exactly what a production
/// DKG removes. Mirror of `frost.rs`'s `FrostTestDealer`, with the Shamir
/// polynomial's coefficients living in the module `R_q^ℓ` and evaluation
/// points the constant polynomials `1..=n` (whose pairwise differences are
/// units in `R_q` since `q` is prime and `n < q` — the "everywhere-short"
/// linear reconstruction's invertibility, minus the shortness, which is the
/// norm carrier and out of scope here).
pub struct HermineTestDealer {
    /// The public matrix `A : R_q^ℓ → R_q^k`.
    pub a: Matrix,
    /// The group public key `t = A·s` (the Lean `A s`).
    pub group_key: PolyVec,
    /// The signing threshold `t` (shares needed to reconstruct at 0).
    pub threshold: u64,
    /// All dealt shares, index `i+1` at position `i`.
    pub shares: Vec<HermineShare>,
    /// The group secret `s = f(0)` — retained ONLY so tests can witness the
    /// reconstruction identity and the extractor's recovered secret. A real
    /// dealer must destroy this; a real scheme never materializes it.
    #[cfg_attr(not(test), allow(dead_code))]
    group_secret: PolyVec,
}

impl HermineTestDealer {
    /// Deal an `n`-member committee with threshold `t`, public matrix
    /// `rows × cols`, deterministically from `seed`.
    ///
    /// The group secret is SHORT (`‖s‖∞ ≤` [`SECRET_ETA`], the MLWE shape) —
    /// that is what makes the smudging shift `‖c·s‖∞` bounded and the
    /// signature norm accounting non-vacuous. The Shamir blinding
    /// coefficients (and hence the SHARES) stay full-range: only the
    /// reconstructed `Σ λ_i·s_i = s` enters the combined signature.
    pub fn deal(rows: usize, cols: usize, n: u64, t: u64, seed: u64) -> Option<Self> {
        // Domain-separate the secret's randomness from the matrix/blinding
        // stream (which deal_with_group_secret re-derives from `seed`).
        let mut state = seed.wrapping_mul(0x2545f4914f6cdd1d) ^ 0x5ec2e7;
        let group_secret = sample_short_vec(&mut state, cols, SECRET_ETA);
        Self::deal_with_group_secret(rows, cols, n, t, seed, group_secret)
    }

    /// Deal with a CALLER-CHOSEN group secret (the Shamir constant term);
    /// blinding coefficients and the public matrix still come from `seed`.
    ///
    /// This exists so tests can put two dealers on the same public shape
    /// with two known secrets `s₀ ≠ s₁` and witness the smudging bound
    /// empirically. Callers wanting the norm accounting to mean anything
    /// must choose a SHORT secret.
    pub fn deal_with_group_secret(
        rows: usize,
        cols: usize,
        n: u64,
        t: u64,
        seed: u64,
        group_secret: PolyVec,
    ) -> Option<Self> {
        if t == 0 || t > n || n >= Q || rows == 0 || cols == 0 || group_secret.len() != cols {
            return None;
        }
        let mut state = seed;
        let a = Matrix::from_fn(rows, cols, |_, _| sample_poly(&mut state));
        // f(x) = a_0 + a_1·x + … + a_{t-1}·x^{t-1}, coefficients in R_q^ℓ;
        // a_0 is the group secret, the blinding coefficients are full-range.
        let mut coeffs: Vec<PolyVec> = vec![group_secret];
        coeffs.extend((1..t).map(|_| sample_vec(&mut state, cols)));
        let eval = |x: &Poly| -> PolyVec {
            // Horner over the module.
            coeffs
                .iter()
                .rev()
                .fold(PolyVec::zero(cols), |acc, c| acc.scale(x).add(c))
        };
        let group_secret = coeffs[0].clone();
        let group_key = a.mul_vec(&group_secret);
        let shares = (1..=n)
            .map(|i| HermineShare {
                index: i,
                share: eval(&Poly::constant(i)),
            })
            .collect();
        Some(Self {
            a,
            group_key,
            threshold: t,
            shares,
            group_secret,
        })
    }

    /// Lagrange-reconstruct `Σ λ_i • s_i` over a share subset — the Lean
    /// `hrecon` right-hand side. Equals the group secret iff the subset
    /// carries ≥ threshold genuine shares.
    pub fn reconstruct(shares: &[&HermineShare]) -> PolyVec {
        let parts: Vec<u64> = shares.iter().map(|s| s.index).collect();
        shares
            .iter()
            .map(|s| {
                s.share
                    .scale(&Poly::constant(lagrange_at_zero(s.index, &parts)))
            })
            .reduce(|acc, v| acc.add(&v))
            .expect("reconstruct requires a nonempty subset")
    }

    /// Test-only witness of the dealt secret (see the field doc).
    #[cfg(test)]
    pub(crate) fn group_secret(&self) -> &PolyVec {
        &self.group_secret
    }
}

/// The Lagrange coefficient at 0 for participant `i` over the index set
/// `parts`, computed in `ℤ_q` (evaluation points are constants, so the
/// coefficient embeds into `R_q` as a constant — the Lean `lam i : R`).
fn lagrange_at_zero(i: u64, parts: &[u64]) -> u64 {
    let mut num = 1u64;
    let mut den = 1u64;
    for &j in parts {
        if j == i {
            continue;
        }
        num = num * (j % Q) % Q;
        den = den * ((j % Q + Q - i % Q) % Q) % Q;
    }
    num * inv_mod_q(den).expect("distinct indices < q have unit differences") % Q
}

// =============================================================================
// Single-ceremony threshold signing — the Lean theorem's algebra
// =============================================================================

/// A Hermine signature/transcript `(w, c, z)`: commitment, challenge,
/// combined response. [`verify`] accepts it iff `A·z = w + c·t`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HermineSignature {
    /// The combined commitment `w = A·(Σ y_i)` (the Lean `A (∑ masks i)`).
    pub w: PolyVec,
    /// The challenge `c = H(w ‖ t ‖ message)` (a ring element, Lean `c : R`).
    pub c: Poly,
    /// The combined response `z = Σ z_i = Σ (y_i + c·(λ_i·s_i))`.
    pub z: PolyVec,
}

/// Produce a Hermine threshold signature from a signing subset — the Lean
/// `hermine_cert_verifies_under_group_key` algebra with the DEFAULT flooding
/// width [`MASK_WIDTH_WIDE`]. See [`hermine_sign_with_mask_width`].
///
/// SINGLE-CEREMONY, REFERENCE-SAMPLING ONLY — see the module boundary doc.
/// `mask_seed` must be fresh per ceremony (mask reuse across two DIFFERENT
/// challenges hands out the secret — that leak IS the extractor identity
/// this crate's tests witness).
pub fn hermine_sign(
    a: &Matrix,
    group_key: &PolyVec,
    signers: &[&HermineShare],
    mask_seed: u64,
    message: &[u8],
) -> Option<HermineSignature> {
    hermine_sign_with_mask_width(a, group_key, signers, mask_seed, message, MASK_WIDTH_WIDE)
}

/// [`hermine_sign`] with an explicit noise-flooding width `M`.
///
/// Each participant `i ∈ parts` contributes a FLOODED mask `y_i` — every
/// coefficient uniform over `[-M/2, M/2)` ([`sample_wide_mask`]; derived
/// from `mask_seed` and its index, NOT from the message — so re-signing a
/// different message under the same seed forks the transcript at the
/// challenge, exactly the extractor's hypothesis). The ceremony forms
/// `w = A·(Σ y_i)`, the challenge `c = H(w ‖ t ‖ M)`, partial responses
/// `z_i = y_i + c·(λ_i·s_i)`, and the certificate `(w, c, z = Σ z_i)`.
///
/// The Lean `Smudging.smudge_bound` says what `M` buys: the response
/// distribution under two secrets differs by `≤ ‖c·Δs‖∞ / M` — callers pick
/// `M` to dwarf the shift (and the key-hiding test demonstrates the leak a
/// narrow `M` reopens). `M` must be even, in `[2, q]`. Exposed primarily so
/// tests can turn the flooding knob; everything else should use
/// [`hermine_sign`].
pub fn hermine_sign_with_mask_width(
    a: &Matrix,
    group_key: &PolyVec,
    signers: &[&HermineShare],
    mask_seed: u64,
    message: &[u8],
    mask_width: u64,
) -> Option<HermineSignature> {
    if mask_width < 2 || !mask_width.is_multiple_of(2) || mask_width > Q {
        return None;
    }
    sign_ceremony(a, group_key, signers, message, |index| {
        let mut state = mask_seed ^ index.wrapping_mul(0x9e3779b97f4a7c15);
        sample_wide_mask_vec(&mut state, a.cols, mask_width)
    })
}

/// [`hermine_sign`] with DISCRETE-GAUSSIAN noise-flooding of width `sigma` —
/// the production-shaped variant (Raccoon/Hermine deploy Gaussian flooding
/// for its tighter Rényi-divergence parameter accounting).
///
/// Identical ceremony to the uniform path; only the mask DISTRIBUTION
/// changes: each mask coefficient comes from a centered [`DiscreteGaussian`]
/// of width `sigma` (CDT method, tail-cut `⌈τσ⌉`, τ =
/// [`GAUSSIAN_TAIL_CUT`]). The hiding story is the Gaussian analogue of the
/// Lean `smudge_bound`: per coefficient, `TV ≲ ‖c·Δs‖∞ / (σ√(2π))` — narrow
/// σ leaks the secret, wide σ hides it (witnessed empirically by the
/// key-hiding test). The shortness story: every mask coefficient is
/// tail-bounded by `T = ⌈τσ⌉`, so the combined honest response obeys
/// [`acceptance_bound`]`(num_signers, 2·T, shift_bound)`.
///
/// NOTE the Lean `Smudging` spec pins the UNIFORM+TV leg only; this path is
/// spec-shaped but its bound is witnessed empirically, not Lean-pinned.
/// `None` if [`DiscreteGaussian::new`] rejects `sigma` or the signer set is
/// degenerate. Same reference boundary as everything here: splitmix64, not
/// constant-time.
pub fn hermine_sign_gaussian(
    a: &Matrix,
    group_key: &PolyVec,
    signers: &[&HermineShare],
    mask_seed: u64,
    message: &[u8],
    sigma: f64,
) -> Option<HermineSignature> {
    let gauss = DiscreteGaussian::new(sigma)?;
    sign_ceremony(a, group_key, signers, message, |index| {
        let mut state = mask_seed ^ index.wrapping_mul(0x9e3779b97f4a7c15);
        sample_gaussian_mask_vec(&mut state, a.cols, &gauss)
    })
}

/// The shared single-ceremony core: validate the signer set, draw each
/// signer's mask via `mask_for(index)`, form `w = A·(Σ y_i)`, the challenge,
/// the Lagrange-weighted partials, and the combined certificate. The two
/// public entry points differ ONLY in the mask distribution they plug in.
fn sign_ceremony(
    a: &Matrix,
    group_key: &PolyVec,
    signers: &[&HermineShare],
    message: &[u8],
    mut mask_for: impl FnMut(u64) -> PolyVec,
) -> Option<HermineSignature> {
    if signers.is_empty() {
        return None;
    }
    let parts: Vec<u64> = signers.iter().map(|s| s.index).collect();
    // Distinct indices only (a duplicated signer is a caller bug, not a quorum).
    {
        let mut seen = std::collections::HashSet::new();
        if !parts.iter().all(|i| seen.insert(*i)) {
            return None;
        }
    }

    // Round 1: flooded masks + combined commitment.
    let masks: Vec<PolyVec> = signers.iter().map(|s| mask_for(s.index)).collect();
    let y_sum = masks
        .iter()
        .fold(PolyVec::zero(a.cols), |acc, y| acc.add(y));
    let w = a.mul_vec(&y_sum);

    // Challenge under the GROUP key.
    let c = challenge(&w, group_key, message);

    // Round 2: Lagrange-weighted partials z_i = y_i + c·(λ_i·s_i), summed.
    let z = signers
        .iter()
        .zip(masks.iter())
        .map(|(s, y)| partial_response(s, &parts, y, &c))
        .reduce(|acc, zi| acc.add(&zi))
        .expect("nonempty signer set");

    Some(HermineSignature { w, c, z })
}

/// Signer `i`'s partial response `z_i = y_i + c·(λ_i·s_i)` — the Lean
/// `masks i + c • (lam i • shares i)`, one summand of the certificate.
/// Exposed so tests can witness `hermine_share_is_valid_under_key_share`.
pub fn partial_response(signer: &HermineShare, parts: &[u64], mask: &PolyVec, c: &Poly) -> PolyVec {
    let lam = Poly::constant(lagrange_at_zero(signer.index, parts));
    mask.add(&signer.share.scale(&lam).scale(c))
}

/// Verify a Hermine signature against the group key: recompute the challenge
/// from `(w, t, message)` and check the Lean relation `A·z = w + c·t`.
pub fn verify_hermine(
    a: &Matrix,
    group_key: &PolyVec,
    message: &[u8],
    sig: &HermineSignature,
) -> bool {
    sig.c == challenge(&sig.w, group_key, message) && verify(a, group_key, &sig.w, &sig.c, &sig.z)
}

// =============================================================================
// Shortness accounting — the concrete Lattice.ShortNorm carrier
// =============================================================================

/// The signature's L∞ norm in centered representation, `‖z‖∞` — the concrete
/// realization of the norm the Lean spec leaves abstract (the
/// `Lattice.ShortNorm` carrier; what makes an extracted `z − z'` an MSIS
/// witness rather than an arbitrary ring element).
pub fn signature_norm(z: &PolyVec) -> u64 {
    z.norm_inf()
}

/// The honest-signature acceptance bound for the combined response of
/// `num_signers` flooded parties: `‖z‖∞ ≤ num_signers·(M/2) + shift_bound`,
/// where `shift_bound ≥ ‖c·s‖∞` (for ternary `c` and `‖s‖∞ ≤ η`,
/// `shift_bound = N·η` works, since a negacyclic product's coefficient is a
/// ±sum of `N` coefficient products).
///
/// This bound only SAYS anything when it is `< ⌊q/2⌋` (every centered
/// element clears that ceiling for free) — the flooding-width choice in
/// [`MASK_WIDTH_WIDE`] keeps it there at threshold-sized signer sets, and
/// the tests assert non-vacuity explicitly.
pub fn acceptance_bound(num_signers: u64, mask_width: u64, shift_bound: u64) -> u64 {
    num_signers * (mask_width / 2) + shift_bound
}

// =============================================================================
// The special-soundness extractor (HermineExtractor.lean)
// =============================================================================

/// The extracted lattice relation from two forked transcripts sharing a
/// commitment: returns `(A·(z − z'), (c − c')·t)` — the two sides of the Lean
/// `hermine_special_soundness_extracts_relation` conclusion
/// `A (z - z') = (c - c') • t`. Both accepting transcripts make them equal;
/// the SHORTNESS of `z − z'` (what makes it an MSIS break) is the norm
/// carrier, out of scope.
pub fn extracted_relation(
    a: &Matrix,
    group_key: &PolyVec,
    fork1: &HermineSignature,
    fork2: &HermineSignature,
) -> (PolyVec, PolyVec) {
    let lhs = a.mul_vec(&fork1.z.sub(&fork2.z));
    let rhs = group_key.scale(&fork1.c.sub(&fork2.c));
    (lhs, rhs)
}

/// The Lean `extractPreimage c c' z z' = (c - c')⁻¹ • (z - z')`, realized on
/// the constant-unit subring (this reference's stand-in for the deployed
/// challenge set's unit-difference property; the Lean `FieldModel` takes a
/// field). `None` if `c − c'` is not a constant unit.
pub fn extract_preimage(
    c: &Poly,
    c_prime: &Poly,
    z: &PolyVec,
    z_prime: &PolyVec,
) -> Option<PolyVec> {
    let inv = c.sub(c_prime).inverse_constant()?;
    Some(z.sub(z_prime).scale(&inv))
}

// =============================================================================
// Tests — the Lean spec's identities, witnessed on concrete R_q
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// k=2, ℓ=3, n=5 members, threshold t=3, deterministic seed.
    fn dealer_5_of_3() -> HermineTestDealer {
        HermineTestDealer::deal(2, 3, 5, 3, 0xd7e6_6001).unwrap()
    }

    // -- (a) correctness: hermine_cert_verifies_under_group_key ------------

    #[test]
    fn honest_threshold_signature_verifies() {
        let d = dealer_5_of_3();
        let message = b"dregg-federation-vote-v1:hermine";
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &signers, 0xAA11, message).unwrap();
        assert!(verify_hermine(&d.a, &d.group_key, message, &sig));
        // And the raw Lean relation directly, not just via the wrapper.
        assert!(verify(&d.a, &d.group_key, &sig.w, &sig.c, &sig.z));
    }

    #[test]
    fn any_t_subset_verifies_no_dependence_on_which_subset() {
        // The Lean theorem has NO dependence on t, n, or which subset signed.
        let d = dealer_5_of_3();
        let message = b"subset independence";
        for subset in [[0usize, 1, 2], [0, 2, 4], [1, 3, 4]] {
            let signers: Vec<&HermineShare> = subset.iter().map(|&i| &d.shares[i]).collect();
            let sig = hermine_sign(
                &d.a,
                &d.group_key,
                &signers,
                0xBB00 + subset[0] as u64,
                message,
            )
            .unwrap();
            assert!(verify_hermine(&d.a, &d.group_key, message, &sig));
        }
        // Supra-threshold subsets verify too (linear reconstruction is exact).
        let all: Vec<&HermineShare> = d.shares.iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &all, 0xCC00, message).unwrap();
        assert!(verify_hermine(&d.a, &d.group_key, message, &sig));
    }

    #[test]
    fn wrong_message_fails() {
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &signers, 0xDD00, b"correct").unwrap();
        assert!(!verify_hermine(&d.a, &d.group_key, b"wrong", &sig));
    }

    #[test]
    fn tampered_response_fails_the_relation() {
        let d = dealer_5_of_3();
        let message = b"tamper";
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let mut sig = hermine_sign(&d.a, &d.group_key, &signers, 0xEE00, message).unwrap();
        sig.z.0[0] = sig.z.0[0].add(&Poly::constant(1));
        assert!(!verify_hermine(&d.a, &d.group_key, message, &sig));
    }

    // -- hermine_share_is_valid_under_key_share (identifiable abort) -------

    #[test]
    fn partial_is_valid_signature_under_its_key_share() {
        // z_i = y_i + c·(λ_i·s_i) verifies under key share A·(λ_i·s_i) with
        // commitment A·y_i — so a bad share is caught by verifying it alone.
        let d = dealer_5_of_3();
        let parts = [1u64, 2, 3];
        let c = {
            let mut c = Poly::constant(7);
            c.coeffs[1] = 5;
            c.coeffs[N / 2] = 11;
            c.coeffs[N - 1] = 2;
            c
        };
        for signer in &d.shares[0..3] {
            let mut state = 0x51_6E45 ^ signer.index;
            let mask = super::sample_vec(&mut state, d.a.cols);
            let z_i = partial_response(signer, &parts, &mask, &c);
            let key_share = signer.key_share(&d.a, &parts);
            let w_i = d.a.mul_vec(&mask);
            assert!(verify(&d.a, &key_share, &w_i, &c, &z_i));
        }
    }

    // -- (b) the extractor identity: HermineExtractor.lean -----------------

    #[test]
    fn forked_transcripts_satisfy_the_extractor_relation() {
        // Same mask seed, two different messages → same commitment w,
        // different challenges — the forking-lemma transcript pair. The Lean
        // hermine_special_soundness_extracts_relation:
        //   A·(z − z') = (c − c')·t.
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[1..4].iter().collect();
        let seed = 0xF0F0;
        let sig1 = hermine_sign(&d.a, &d.group_key, &signers, seed, b"fork-msg-1").unwrap();
        let sig2 = hermine_sign(&d.a, &d.group_key, &signers, seed, b"fork-msg-2").unwrap();
        // Both accept; shared commitment; distinct challenges.
        assert!(verify_hermine(&d.a, &d.group_key, b"fork-msg-1", &sig1));
        assert!(verify_hermine(&d.a, &d.group_key, b"fork-msg-2", &sig2));
        assert_eq!(sig1.w, sig2.w);
        assert_ne!(sig1.c, sig2.c);
        // The extracted relation holds.
        let (lhs, rhs) = extracted_relation(&d.a, &d.group_key, &sig1, &sig2);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn extractor_recovers_the_secret_on_constant_challenge_forks() {
        // The Lean FieldModel extractor_recovers_secret: with a unit
        // difference, extractPreimage on honest responses computes s itself.
        // Constant challenges make c − c' a constant unit in R_q.
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let parts: Vec<u64> = signers.iter().map(|s| s.index).collect();
        let c1 = Poly::constant(19);
        let c2 = Poly::constant(1001);
        let mut masks = Vec::new();
        for s in &signers {
            let mut state = 0xE47_AC7 ^ s.index;
            masks.push(super::sample_vec(&mut state, d.a.cols));
        }
        let respond = |c: &Poly| -> PolyVec {
            signers
                .iter()
                .zip(masks.iter())
                .map(|(s, y)| partial_response(s, &parts, y, c))
                .reduce(|a, b| a.add(&b))
                .unwrap()
        };
        let (z1, z2) = (respond(&c1), respond(&c2));
        let recovered = extract_preimage(&c1, &c2, &z1, &z2).unwrap();
        // The recovered witness IS the group secret, and it maps to t.
        assert_eq!(&recovered, d.group_secret());
        assert_eq!(d.a.mul_vec(&recovered), d.group_key);
    }

    // -- (c) sub-threshold cannot reconstruct or forge ----------------------

    #[test]
    fn sub_threshold_subset_cannot_forge() {
        // 2 shares of a t=3 sharing Lagrange-interpolate a DIFFERENT degree-1
        // polynomial's value at 0, not the group secret: the cert must fail.
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[0..2].iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &signers, 0x5B00, b"m").unwrap();
        assert!(!verify_hermine(&d.a, &d.group_key, b"m", &sig));
        assert!(!verify(&d.a, &d.group_key, &sig.w, &sig.c, &sig.z));
    }

    #[test]
    fn shamir_reconstruction_threshold_boundary() {
        // Any t-subset reconstructs s exactly (the Lean hrecon hypothesis is
        // REAL, not assumed); any (t−1)-subset reconstructs something else.
        let d = dealer_5_of_3();
        for subset in [[0usize, 1, 2], [0, 2, 4], [2, 3, 4]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &d.shares[i]).collect();
            assert_eq!(&HermineTestDealer::reconstruct(&shares), d.group_secret());
        }
        for subset in [[0usize, 1], [1, 4], [2, 3]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &d.shares[i]).collect();
            assert_ne!(&HermineTestDealer::reconstruct(&shares), d.group_secret());
        }
    }

    // -- (d) noise-flooding: Smudging.lean, empirically ---------------------

    /// The worst-case smudging shift bound at these parameters: ternary
    /// challenge (`‖c‖∞ ≤ 1`) times a short secret (`‖s‖∞ ≤ η`), through a
    /// negacyclic product whose every coefficient is a ±sum of `N` terms.
    const SHIFT_BOUND: u64 = (N as u64) * SECRET_ETA;

    #[test]
    fn wide_mask_coefficients_are_centered_and_bounded() {
        for m in [16u64, 512, MASK_WIDTH_WIDE] {
            let mut state = 0xA5A5_0001;
            let (mut lo, mut hi) = (i64::MAX, i64::MIN);
            for _ in 0..500 {
                let p = sample_wide_mask(&mut state, m);
                for i in 0..N {
                    let v = p.centered_coeff(i);
                    assert!(-((m / 2) as i64) <= v && v < (m / 2) as i64);
                    lo = lo.min(v);
                    hi = hi.max(v);
                }
            }
            // Both halves of the centered range are actually exercised.
            assert!(lo < 0 && hi > 0);
        }
    }

    #[test]
    fn honest_signature_is_short_under_the_acceptance_bound() {
        // The shortness leg: with flooding width M and t signers, the
        // combined honest response obeys ‖z‖∞ ≤ t·(M/2) + ‖c·s‖∞ — and at
        // these parameters that bound is BELOW the ⌊q/2⌋ ceiling, so it has
        // teeth (a full-range vector violates it).
        let d = dealer_5_of_3();
        let bound = acceptance_bound(3, MASK_WIDTH_WIDE, SHIFT_BOUND);
        assert!(bound < Q / 2, "acceptance bound must be non-vacuous");
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        for seed in 0..50u64 {
            let sig =
                hermine_sign(&d.a, &d.group_key, &signers, 0x5407_0000 + seed, b"short-z").unwrap();
            assert!(verify_hermine(&d.a, &d.group_key, b"short-z", &sig));
            assert!(signature_norm(&sig.z) <= bound);
        }
        // Teeth: a full-range (unflooded, q-wide) vector blows the bound.
        let mut state = 0xFEED_F00D;
        let full_range = super::sample_vec(&mut state, d.a.cols);
        assert!(signature_norm(&full_range) > bound);
    }

    #[test]
    fn extracted_difference_is_short() {
        // The MSIS-witness leg: forked transcripts share masks, so
        // z − z' = (c − c')·s — short because c, c' are ternary and s is
        // short: ‖z − z'‖∞ ≤ N·2·η, far inside the generic 2×acceptance
        // bound a verifier derives from two accepted signatures.
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[1..4].iter().collect();
        let seed = 0xF0F1;
        let sig1 = hermine_sign(&d.a, &d.group_key, &signers, seed, b"norm-fork-1").unwrap();
        let sig2 = hermine_sign(&d.a, &d.group_key, &signers, seed, b"norm-fork-2").unwrap();
        assert_eq!(sig1.w, sig2.w);
        assert_ne!(sig1.c, sig2.c);
        let diff = sig1.z.sub(&sig2.z);
        assert!(signature_norm(&diff) <= 2 * SHIFT_BOUND);
        assert!(signature_norm(&diff) <= 2 * acceptance_bound(3, MASK_WIDTH_WIDE, SHIFT_BOUND));
        // And the extractor relation holds under flooding, unchanged.
        let (lhs, rhs) = extracted_relation(&d.a, &d.group_key, &sig1, &sig2);
        assert_eq!(lhs, rhs);
    }

    /// Empirical total-variation distance between two samples over `k`
    /// equiprobable bins derived from the POOLED sample — scale-free binning,
    /// so the same estimator serves the narrow and the wide distributions.
    fn empirical_tv(xs: &[i64], ys: &[i64], k: usize) -> f64 {
        let mut pooled: Vec<i64> = xs.iter().chain(ys.iter()).copied().collect();
        pooled.sort_unstable();
        let edges: Vec<i64> = (1..k).map(|i| pooled[i * pooled.len() / k]).collect();
        let bucket = |v: i64| edges.partition_point(|&e| e <= v);
        let (mut px, mut py) = (vec![0f64; k], vec![0f64; k]);
        for &x in xs {
            px[bucket(x)] += 1.0 / xs.len() as f64;
        }
        for &y in ys {
            py[bucket(y)] += 1.0 / ys.len() as f64;
        }
        px.iter().zip(&py).map(|(a, b)| (a - b).abs()).sum::<f64>() / 2.0
    }

    /// Sign the same message `count` times (fresh mask seeds) with the given
    /// signing closure and pool ALL centered coefficients of the first `z`
    /// component — the observable whose distribution the Smudging spec
    /// bounds. Pooling coefficients (each carries its own independent mask
    /// noise) gives `count·N` samples per run, which is what keeps the
    /// empirical TV cheap at `N = 64`.
    fn z_coeff_samples(
        d: &HermineTestDealer,
        count: usize,
        mut sign_at: impl FnMut(&HermineTestDealer, u64) -> HermineSignature,
    ) -> Vec<i64> {
        (0..count)
            .flat_map(|i| {
                let sig = sign_at(d, 0x71DE_0000 + i as u64);
                assert!(verify_hermine(
                    &d.a,
                    &d.group_key,
                    b"key-hiding-probe",
                    &sig
                ));
                (0..N).map(move |k| sig.z.0[0].centered_coeff(k))
            })
            .collect()
    }

    /// Two dealers on the same public shape with two known short secrets:
    /// s0 = 0 and s1 with ‖s1‖∞ = η — the key-hiding test pair.
    fn key_hiding_dealer_pair() -> (HermineTestDealer, HermineTestDealer) {
        let (rows, cols, n, t, seed) = (2usize, 3usize, 5u64, 3u64, 0x51_D6E5u64);
        let s0 = PolyVec::zero(cols);
        let s1 = PolyVec(vec![
            Poly {
                coeffs: [SECRET_ETA; N]
            };
            cols
        ]);
        let d0 = HermineTestDealer::deal_with_group_secret(rows, cols, n, t, seed, s0).unwrap();
        let d1 = HermineTestDealer::deal_with_group_secret(rows, cols, n, t, seed, s1).unwrap();
        (d0, d1)
    }

    const KEY_HIDING_SAMPLES: usize = 400; // signatures per distribution; ×N pooled coefficients
    const KEY_HIDING_BINS: usize = 16;

    #[test]
    fn key_hiding_wide_mask_hides_narrow_mask_leaks() {
        // THE Smudging demonstration, UNIFORM leg: the signature
        // distributions under the two secrets differ by ≤ ‖c·Δs‖∞ / M
        // (smudge_bound): wide M makes them statistically indistinguishable;
        // a narrow M (comparable to the shift — the unflooded regime) leaks
        // the secret as a large total-variation gap.
        let (d0, d1) = key_hiding_dealer_pair();
        // Narrow = BELOW the shift bound (‖c·Δs‖∞ ≤ 128): the unflooded
        // regime, where the mask cannot smudge the secret's contribution.
        let m_narrow = 4u64;
        let m_mid = 128u64;
        let tv_at = |m: u64| {
            let samples = |d: &HermineTestDealer| {
                z_coeff_samples(d, KEY_HIDING_SAMPLES, |d, seed| {
                    let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
                    hermine_sign_with_mask_width(
                        &d.a,
                        &d.group_key,
                        &signers,
                        seed,
                        b"key-hiding-probe",
                        m,
                    )
                    .unwrap()
                })
            };
            empirical_tv(&samples(&d0), &samples(&d1), KEY_HIDING_BINS)
        };
        let tv_narrow = tv_at(m_narrow);
        let tv_mid = tv_at(m_mid);
        let tv_wide = tv_at(MASK_WIDTH_WIDE);
        println!(
            "key-hiding TV (uniform): narrow(M={m_narrow}) = {tv_narrow:.4}, \
             mid(M={m_mid}) = {tv_mid:.4}, wide(M={MASK_WIDTH_WIDE}) = {tv_wide:.4}"
        );
        // Wide flooding hides: the gap sits at the sampling-noise floor,
        // far below what any usable distinguisher needs.
        assert!(tv_wide < 0.05, "wide-mask TV too large: {tv_wide}");
        // Narrow mask leaks: the same secrets, glaringly distinguishable.
        assert!(tv_narrow > 0.35, "narrow-mask TV too small: {tv_narrow}");
        // And the leakage SHRINKS as M grows — the smudge_bound ‖c·Δs‖/M
        // in motion.
        assert!(tv_narrow > 3.0 * tv_mid && tv_mid > 3.0 * tv_wide);
    }

    #[test]
    fn key_hiding_gaussian_wide_sigma_hides_narrow_sigma_leaks() {
        // The GAUSSIAN analogue of the smudging demonstration: same two
        // secrets, discrete-Gaussian flooding. Per coefficient the gap is
        // TV ≲ ‖c·Δs‖∞ / (σ√(2π)) — narrow σ leaks, wide σ hides, and the
        // TV shrinks monotonically as σ grows.
        let (d0, d1) = key_hiding_dealer_pair();
        let tv_at = |sigma: f64| {
            let samples = |d: &HermineTestDealer| {
                z_coeff_samples(d, KEY_HIDING_SAMPLES, |d, seed| {
                    let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
                    hermine_sign_gaussian(
                        &d.a,
                        &d.group_key,
                        &signers,
                        seed,
                        b"key-hiding-probe",
                        sigma,
                    )
                    .unwrap()
                })
            };
            empirical_tv(&samples(&d0), &samples(&d1), KEY_HIDING_BINS)
        };
        let sigmas = [2.0f64, 16.0, 128.0, 1024.0];
        let tvs: Vec<f64> = sigmas.iter().map(|&s| tv_at(s)).collect();
        println!(
            "key-hiding TV (gaussian): {}",
            sigmas
                .iter()
                .zip(&tvs)
                .map(|(s, tv)| format!("sigma={s} -> {tv:.4}"))
                .collect::<Vec<_>>()
                .join(", ")
        );
        // Narrow sigma (below the typical shift magnitude) leaks hard.
        assert!(tvs[0] > 0.35, "narrow-sigma TV too small: {}", tvs[0]);
        // Wide sigma hides down to the sampling-noise floor.
        assert!(
            *tvs.last().unwrap() < 0.05,
            "wide-sigma TV too large: {}",
            tvs.last().unwrap()
        );
        // And the leakage shrinks as sigma grows — the Gaussian smudging
        // trade in motion.
        for pair in tvs.windows(2) {
            assert!(
                pair[0] > pair[1],
                "TV must shrink with sigma: {:?} at sigmas {:?}",
                tvs,
                sigmas
            );
        }
    }

    // -- the Gaussian sampler itself ----------------------------------------

    #[test]
    fn gaussian_sampler_matches_its_moments_and_tail() {
        for sigma in [2.0f64, 16.0, 256.0] {
            let gauss = DiscreteGaussian::new(sigma).unwrap();
            let mut state = 0x6A_0551A2u64 ^ sigma.to_bits();
            const COUNT: usize = 40_000;
            let (mut sum, mut sum_sq) = (0f64, 0f64);
            let (mut lo, mut hi) = (i64::MAX, i64::MIN);
            for _ in 0..COUNT {
                let v = gauss.sample(&mut state);
                assert!(v.abs() <= gauss.tail_bound(), "tail cut violated");
                sum += v as f64;
                sum_sq += (v * v) as f64;
                lo = lo.min(v);
                hi = hi.max(v);
            }
            let mean = sum / COUNT as f64;
            let var = sum_sq / COUNT as f64 - mean * mean;
            // Centered: mean within a few standard errors of 0.
            assert!(
                mean.abs() < 4.0 * sigma / (COUNT as f64).sqrt(),
                "sigma={sigma}: mean {mean} off-center"
            );
            // Width: sample variance within 10% of σ² (discrete ≈ continuous
            // for σ ≥ 2; sampling error at 40k samples is ~1%).
            assert!(
                (var - sigma * sigma).abs() < 0.1 * sigma * sigma,
                "sigma={sigma}: variance {var} vs sigma^2 {}",
                sigma * sigma
            );
            // Both signs actually exercised.
            assert!(lo < 0 && hi > 0);
        }
    }

    #[test]
    fn gaussian_sampler_rejects_degenerate_widths() {
        assert!(DiscreteGaussian::new(0.0).is_none());
        assert!(DiscreteGaussian::new(-1.0).is_none());
        assert!(DiscreteGaussian::new(f64::NAN).is_none());
        assert!(DiscreteGaussian::new(f64::INFINITY).is_none());
        // Tail ⌈τσ⌉ reaching ⌊q/2⌋ would alias under centered reduction.
        assert!(DiscreteGaussian::new((Q / 2) as f64 / GAUSSIAN_TAIL_CUT + 1.0).is_none());
        assert!(DiscreteGaussian::new(64.0).is_some());
    }

    #[test]
    fn gaussian_signature_verifies_and_is_short() {
        // The ceremony algebra is distribution-blind: the Gaussian path
        // produces verifying signatures, short under the tail-cut bound
        // t·T + shift (= acceptance_bound with mask "width" 2T).
        let d = dealer_5_of_3();
        let sigma = 512.0;
        let tail = DiscreteGaussian::new(sigma).unwrap().tail_bound() as u64;
        let bound = acceptance_bound(3, 2 * tail, SHIFT_BOUND);
        assert!(
            bound < Q / 2,
            "gaussian acceptance bound must be non-vacuous"
        );
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        for seed in 0..25u64 {
            let sig = hermine_sign_gaussian(
                &d.a,
                &d.group_key,
                &signers,
                0x6055_0000 + seed,
                b"gaussian-z",
                sigma,
            )
            .unwrap();
            assert!(verify_hermine(&d.a, &d.group_key, b"gaussian-z", &sig));
            assert!(signature_norm(&sig.z) <= bound);
        }
        // And the forked-transcript extractor identity holds unchanged.
        let sig1 = hermine_sign_gaussian(&d.a, &d.group_key, &signers, 0xF0F2, b"g-fork-1", sigma)
            .unwrap();
        let sig2 = hermine_sign_gaussian(&d.a, &d.group_key, &signers, 0xF0F2, b"g-fork-2", sigma)
            .unwrap();
        assert_eq!(sig1.w, sig2.w);
        assert_ne!(sig1.c, sig2.c);
        let (lhs, rhs) = extracted_relation(&d.a, &d.group_key, &sig1, &sig2);
        assert_eq!(lhs, rhs);
    }

    // -- harness hygiene (mirroring frost.rs's refusals) ---------------------

    #[test]
    fn duplicate_signer_is_refused() {
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = vec![&d.shares[0], &d.shares[0], &d.shares[1]];
        assert!(hermine_sign(&d.a, &d.group_key, &signers, 0x1111, b"m").is_none());
    }

    #[test]
    fn empty_signer_set_is_refused() {
        let d = dealer_5_of_3();
        assert!(hermine_sign(&d.a, &d.group_key, &[], 0x2222, b"m").is_none());
    }

    #[test]
    fn degenerate_dealer_parameters_are_refused() {
        assert!(HermineTestDealer::deal(2, 3, 5, 0, 1).is_none()); // t = 0
        assert!(HermineTestDealer::deal(2, 3, 3, 4, 1).is_none()); // t > n
        assert!(HermineTestDealer::deal(0, 3, 5, 3, 1).is_none()); // no rows
        assert!(HermineTestDealer::deal(2, 0, 5, 3, 1).is_none()); // no cols
        assert!(HermineTestDealer::deal(2, 3, Q, 2, 1).is_none()); // n ≥ q
    }
}
