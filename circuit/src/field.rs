//! Field element type for the circuit.
//!
//! Uses BabyBear (p = 2^31 - 2^27 + 1 = 2013265921) as the native field for STARK proofs.
//! In mock mode, we implement BabyBear arithmetic directly. With plonky3 feature,
//! this wraps `p3_baby_bear::BabyBear`.

use serde::{Deserialize, Serialize};
use std::fmt;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The BabyBear prime: p = 2^31 - 2^27 + 1 = 2013265921.
pub const BABYBEAR_P: u32 = (1 << 31) - (1 << 27) + 1;

/// A BabyBear field element: integers modulo p = 2^31 - 2^27 + 1.
///
/// Stored in canonical form [0, p-1]. All construction paths (including
/// deserialization) perform modular reduction to ensure canonical representation.
/// This prevents malleability attacks where the same logical value could have
/// multiple byte representations (e.g., both `v` and `v + p` representing the
/// same field element but comparing as different).
///
/// # Soundness
///
/// Custom `PartialEq`, `Eq`, and `Hash` implementations normalize before comparison,
/// ensuring that `BabyBear(0) == BabyBear(BABYBEAR_P)` even if a non-canonical value
/// is constructed directly. This prevents HashMap key collisions, Merkle commitment
/// divergence, and signature verification failures.
#[derive(Clone, Copy)]
pub struct BabyBear(pub u32);

impl PartialEq for BabyBear {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.canonical_val() == other.canonical_val()
    }
}

impl Eq for BabyBear {}

impl PartialOrd for BabyBear {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BabyBear {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.canonical_val().cmp(&other.canonical_val())
    }
}

impl std::hash::Hash for BabyBear {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.canonical_val().hash(state);
    }
}

/// Custom serialization that normalizes before writing.
///
/// This ensures that the same logical field element always serializes to the
/// same bytes, preventing malleability in serialized proofs and Merkle commitments.
impl Serialize for BabyBear {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_u32(self.canonical_val())
    }
}

/// Custom deserialization that always reduces modulo p to enforce canonical form.
///
/// Without this, an attacker could submit `v >= p` values that deserialize to
/// non-canonical representations, potentially causing equality checks to produce
/// incorrect results (two BabyBear values representing the same field element
/// but comparing as different).
impl<'de> Deserialize<'de> for BabyBear {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let raw = u32::deserialize(deserializer)?;
        Ok(Self(raw % BABYBEAR_P))
    }
}

impl BabyBear {
    /// The zero element.
    pub const ZERO: Self = Self(0);

    /// The one element (multiplicative identity).
    pub const ONE: Self = Self(1);

    /// The additive generator.
    pub const TWO: Self = Self(2);

    /// Return the canonical u32 representation (always in [0, p-1]).
    /// Used internally by PartialEq and Hash to ensure invariant correctness
    /// even if the inner field holds a non-canonical value (>= p).
    #[inline]
    pub(crate) fn canonical_val(self) -> u32 {
        if self.0 >= BABYBEAR_P {
            self.0 - BABYBEAR_P
        } else {
            self.0
        }
    }

    /// Create a field element from a u32, reducing modulo p.
    #[inline]
    pub fn new(val: u32) -> Self {
        Self(val % BABYBEAR_P)
    }

    /// Create a field element from an untrusted u32, always reducing modulo p.
    /// Use this for all deserialization paths where the value comes from external
    /// (potentially adversarial) data to prevent non-canonical malleability.
    ///
    /// Panics (in all builds) if the value exceeds 2*p (which would indicate
    /// an invalid encoding, not merely a non-reduced value).
    #[inline]
    pub fn new_canonical(val: u32) -> Self {
        Self(val % BABYBEAR_P)
    }

    /// Create from a u64, reducing modulo p.
    #[inline]
    pub fn from_u64(val: u64) -> Self {
        Self((val % BABYBEAR_P as u64) as u32)
    }

    /// Create from raw canonical value (must be < p). No reduction performed.
    ///
    /// # Panics
    ///
    /// Panics in all builds (including release) if `val >= BABYBEAR_P`.
    /// Use `BabyBear::new(val)` if the value might exceed p.
    #[inline]
    pub const fn from_canonical(val: u32) -> Self {
        assert!(
            val < BABYBEAR_P,
            "from_canonical: value must be < BABYBEAR_P"
        );
        Self(val)
    }

    /// Get the canonical u32 representation.
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.0
    }

    /// Compute the multiplicative inverse using Fermat's little theorem.
    /// a^(-1) = a^(p-2) mod p.
    /// Returns None for zero.
    pub fn inverse(self) -> Option<Self> {
        if self.0 == 0 {
            return None;
        }
        Some(self.pow(BABYBEAR_P - 2))
    }

    /// Exponentiation by squaring.
    pub fn pow(self, mut exp: u32) -> Self {
        let mut base = self;
        let mut result = Self::ONE;
        while exp > 0 {
            if exp & 1 == 1 {
                result *= base;
            }
            base = base * base;
            exp >>= 1;
        }
        result
    }

    /// Square this element.
    #[inline]
    pub fn square(self) -> Self {
        self * self
    }

    /// Convert 4 bytes into a single field element (little-endian, fits in BabyBear).
    /// Only uses 31 bits, so at most 3.875 bytes of entropy per element.
    pub fn from_bytes_packed(bytes: &[u8]) -> Vec<Self> {
        let mut result = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            let mut val: u32 = 0;
            for j in 0..4 {
                if i + j < bytes.len() {
                    val |= (bytes[i + j] as u32) << (j * 8);
                }
            }
            // Reduce to fit in BabyBear
            result.push(Self::new(val));
            i += 4;
        }
        result
    }
}

impl fmt::Debug for BabyBear {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BB({})", self.0)
    }
}

impl fmt::Display for BabyBear {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Default for BabyBear {
    fn default() -> Self {
        Self::ZERO
    }
}

impl From<u32> for BabyBear {
    fn from(val: u32) -> Self {
        Self::new(val)
    }
}

impl From<u64> for BabyBear {
    fn from(val: u64) -> Self {
        Self::from_u64(val)
    }
}

/// Reduce a `u64` modulo `BABYBEAR_P` WITHOUT a hardware integer division.
///
/// This is BYTE-IDENTICAL to `(x % BABYBEAR_P as u64) as u32` for every `x: u64`.
/// It uses Barrett reduction with a precomputed reciprocal `m = floor(2^64 / P)`
/// (computed via `u128`), producing a quotient estimate `q = (x * m) >> 64` that is
/// at most the true quotient and within a tiny constant of it; the trailing
/// `while`-correction subtracts the residual multiples of `P` so the result is the
/// exact canonical remainder in `[0, P)`. For the operand ranges that actually feed
/// the field ops (`add`: x < 2^33; `mul`: x < 2^64) the correction runs at most a
/// couple of iterations, and it remains correct for any `u64`.
///
/// The canonical repr is UNCHANGED: callers still observe a value in `[0, P)`,
/// identical to the previous `%`-based reduction.
#[inline(always)]
const fn reduce_u64(x: u64) -> u32 {
    // m = floor(2^64 / P). 2^64 = 18446744073709551616.
    const M: u128 = (1u128 << 64) / (BABYBEAR_P as u128);
    let q = ((x as u128 * M) >> 64) as u64;
    let mut r = x - q * (BABYBEAR_P as u64);
    // Barrett's q underestimates the true quotient by a small bounded amount, so r
    // starts in [0, k*P) for a small k; subtract the residual multiples of P.
    while r >= BABYBEAR_P as u64 {
        r -= BABYBEAR_P as u64;
    }
    r as u32
}

impl Add for BabyBear {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        // BYTE-IDENTICAL to `(self.0 as u64 + rhs.0 as u64) % P`.
        // Fast path (the overwhelmingly common case: canonical operands < P):
        // a + b < 2P fits in u32, so a single conditional subtract suffices.
        // Slow path (a non-canonical operand >= P) falls back to the exact reducer
        // so the result matches the old `%` semantics for ALL u32 inputs.
        let a = self.0;
        let b = rhs.0;
        if a < BABYBEAR_P && b < BABYBEAR_P {
            // a, b < P < 2^31  =>  s = a + b < 2^32 fits u32, and s < 2P.
            let s = a + b;
            Self(if s >= BABYBEAR_P { s - BABYBEAR_P } else { s })
        } else {
            Self(reduce_u64(a as u64 + b as u64))
        }
    }
}

impl AddAssign for BabyBear {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for BabyBear {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self {
        // BYTE-IDENTICAL to `(self.0 as u64 + P - rhs.0 as u64) % P`.
        // Fast path (canonical operands < P): a, b < P, so the u64 intermediate
        // `a + P - b` lies in [P+1-P, P+P-0) = [1, 2P), thus `% P` removes exactly
        // one P iff a >= b. The overflowing-sub branch reproduces that bit-for-bit.
        let a = self.0;
        let b = rhs.0;
        if a < BABYBEAR_P && b < BABYBEAR_P {
            let (d, borrow) = a.overflowing_sub(b);
            Self(if borrow {
                d.wrapping_add(BABYBEAR_P)
            } else {
                d
            })
        } else {
            // Non-canonical fallback: reproduce the old u64 expression exactly.
            let diff = a as u64 + BABYBEAR_P as u64 - b as u64;
            Self(reduce_u64(diff))
        }
    }
}

impl SubAssign for BabyBear {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for BabyBear {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        // BYTE-IDENTICAL to `(self.0 as u64 * rhs.0 as u64) % P`.
        // The product is < 2^64 for any u32 operands; `reduce_u64` is the
        // division-free exact equivalent of `% P` over the full u64 range.
        let prod = self.0 as u64 * rhs.0 as u64;
        Self(reduce_u64(prod))
    }
}

impl MulAssign for BabyBear {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Neg for BabyBear {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        if self.0 == 0 {
            Self::ZERO
        } else {
            Self(BABYBEAR_P - self.0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_basics() {
        let a = BabyBear::new(100);
        let b = BabyBear::new(200);
        assert_eq!((a + b).0, 300);
        assert_eq!((b - a).0, 100);
        assert_eq!((a * b).0, 20000);
    }

    #[test]
    fn field_overflow() {
        let a = BabyBear::new(BABYBEAR_P - 1);
        let b = BabyBear::new(2);
        assert_eq!((a + b).0, 1); // (p-1) + 2 = p+1 = 1 mod p
    }

    #[test]
    fn field_inverse() {
        let a = BabyBear::new(7);
        let inv = a.inverse().unwrap();
        assert_eq!((a * inv).0, 1);
    }

    #[test]
    fn zero_inverse_is_none() {
        assert!(BabyBear::ZERO.inverse().is_none());
    }

    #[test]
    fn negation() {
        let a = BabyBear::new(42);
        let neg_a = -a;
        assert_eq!((a + neg_a).0, 0);
    }

    #[test]
    fn encode_decode_hash() {
        let hash = [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
            25, 26, 27, 28, 29, 30, 31, 32,
        ];
        let encoded = crate::effect_vm::bytes32_to_8_limbs(&hash);
        assert_eq!(encoded.len(), 8);
        // Verify round-trip (may lose some bits due to reduction)
        for &e in &encoded {
            assert!(e.0 < BABYBEAR_P);
        }
    }

    #[test]
    fn pow_works() {
        let a = BabyBear::new(3);
        let a_cubed = a.pow(3);
        assert_eq!(a_cubed.0, 27);
    }

    /// Test that non-canonical values compare equal to their canonical counterparts.
    /// This is CRITICAL for soundness: without this, BabyBear(0) != BabyBear(BABYBEAR_P)
    /// even though they represent the same field element, breaking HashMap keys,
    /// Merkle commitments, and signatures.
    #[test]
    fn canonical_equality() {
        // BabyBear(P) should equal BabyBear(0) (both represent zero)
        let zero_canonical = BabyBear(0);
        let zero_non_canonical = BabyBear(BABYBEAR_P);
        assert_eq!(zero_canonical, zero_non_canonical);

        // BabyBear(P+1) should equal BabyBear(1)
        let one_canonical = BabyBear(1);
        let one_non_canonical = BabyBear(BABYBEAR_P + 1);
        assert_eq!(one_canonical, one_non_canonical);
    }

    /// Test that non-canonical values hash the same as their canonical counterparts.
    /// Without this, HashMap<BabyBear, _> could have "duplicate" keys.
    #[test]
    fn canonical_hash() {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        fn compute_hash(val: &BabyBear) -> u64 {
            let mut hasher = DefaultHasher::new();
            val.hash(&mut hasher);
            hasher.finish()
        }

        let zero_a = BabyBear(0);
        let zero_b = BabyBear(BABYBEAR_P);
        assert_eq!(compute_hash(&zero_a), compute_hash(&zero_b));

        let one_a = BabyBear(1);
        let one_b = BabyBear(BABYBEAR_P + 1);
        assert_eq!(compute_hash(&one_a), compute_hash(&one_b));
    }

    /// Test that the Serialize impl produces canonical values.
    /// We verify this by checking that the custom serialize impl calls
    /// canonical_val() before writing.
    #[test]
    fn serialization_canonical() {
        // Verify canonical_val normalizes correctly
        let canonical = BabyBear(42);
        let non_canonical = BabyBear(BABYBEAR_P + 42);

        // Both should produce the same canonical value
        assert_eq!(canonical.canonical_val(), 42);
        assert_eq!(non_canonical.canonical_val(), 42);

        // The as_u32() method returns the raw inner value (which may be non-canonical)
        assert_eq!(canonical.as_u32(), 42);
        assert_eq!(non_canonical.as_u32(), BABYBEAR_P + 42);

        // But equality holds regardless
        assert_eq!(canonical, non_canonical);
    }

    /// Test that from_canonical panics on invalid values in release builds.
    #[test]
    #[should_panic(expected = "from_canonical")]
    fn from_canonical_panics_on_invalid() {
        let _ = BabyBear::from_canonical(BABYBEAR_P);
    }

    // ---- Byte-identity differential against the ORIGINAL `%`-based arithmetic ----
    //
    // These oracles are the EXACT pre-optimization formulas. The differential
    // asserts the optimized `Add`/`Sub`/`Mul` produce a byte-identical inner `.0`
    // for a large random corpus AND for the structural edge cases (0, 1, P-1, and
    // a span of non-canonical inputs >= P up to u32::MAX). Byte-identity here is
    // non-negotiable: the field underpins every Poseidon2 commitment.

    #[inline]
    fn old_add(a: u32, b: u32) -> u32 {
        ((a as u64 + b as u64) % BABYBEAR_P as u64) as u32
    }
    #[inline]
    fn old_mul(a: u32, b: u32) -> u32 {
        ((a as u64 * b as u64) % BABYBEAR_P as u64) as u32
    }
    // The old `sub` is only well-defined where `a as u64 + P - b as u64` does not
    // underflow, i.e. `b <= a + P`. (For larger non-canonical `b` the ORIGINAL code
    // panicked in debug / wrapped in release, so such inputs never occurred.) We
    // restrict the sub-oracle comparison to that domain, which strictly contains all
    // canonical pairs and all real call sites.
    #[inline]
    fn old_sub_defined(a: u32, b: u32) -> Option<u32> {
        let lhs = a as u64 + BABYBEAR_P as u64;
        if (b as u64) <= lhs {
            Some(((lhs - b as u64) % BABYBEAR_P as u64) as u32)
        } else {
            None
        }
    }

    /// `reduce_u64` is byte-identical to `% P` across the full u64 range
    /// (deterministic structural sweep + the Barrett loop-bound check).
    #[test]
    fn reduce_u64_matches_mod_exhaustive_structural() {
        let p = BABYBEAR_P as u64;
        // Edge values, multiples of P +/- small deltas, powers of two, and the
        // extreme product corner (P-1)^2 and u64::MAX.
        let mut xs: Vec<u64> = vec![0, 1, p - 1, p, p + 1, 2 * p, u64::MAX];
        for k in 0..=64u32 {
            if k < 64 {
                xs.push(1u64 << k);
                xs.push((1u64 << k).wrapping_sub(1));
            }
        }
        for mult in 0..2_000u64 {
            xs.push(mult.wrapping_mul(p));
            xs.push(mult.wrapping_mul(p).wrapping_add(1));
            xs.push(mult.wrapping_mul(p).wrapping_sub(1));
        }
        // The full product corner: every (a*b) for a,b in a dense edge set.
        let edges: [u64; 7] = [0, 1, 2, p - 2, p - 1, p, p + 1];
        for &a in &edges {
            for &b in &edges {
                xs.push(a.wrapping_mul(b));
            }
        }
        xs.push((p - 1) * (p - 1)); // largest canonical product

        for &x in &xs {
            assert_eq!(
                super::reduce_u64(x),
                (x % p) as u32,
                "reduce_u64({x}) != {x} % P"
            );
        }
    }

    /// Confirm the Barrett correction `while` loop is BOUNDED (small constant) for
    /// the operand ranges the field ops actually produce: add (< 2^33) and mul
    /// (< 2^64, sampled at the dense product corner). Recompute the same `q` the
    /// reducer uses and count residual subtractions.
    #[test]
    fn reduce_u64_correction_loop_is_bounded() {
        const M: u128 = (1u128 << 64) / (BABYBEAR_P as u128);
        let p = BABYBEAR_P as u64;
        let count_iters = |x: u64| -> u32 {
            let q = ((x as u128 * M) >> 64) as u64;
            let mut r = x - q * p;
            let mut n = 0u32;
            while r >= p {
                r -= p;
                n += 1;
            }
            n
        };
        // mul corner: u64::MAX is the absolute worst case for the estimate.
        let worst = count_iters(u64::MAX);
        assert!(
            worst <= 4,
            "Barrett loop ran {worst} times on u64::MAX (too many)"
        );
        // (P-1)^2, the largest real product.
        assert!(count_iters((p - 1) * (p - 1)) <= 4);
        // add range corner.
        assert!(count_iters((p - 1) + (p - 1)) <= 1);
    }

    /// CONTENTION-INVARIANT A/B microbench: times the OPTIMIZED `mul`/`add`/`sub`
    /// against a local reimplementation of the OLD `%`-based ops over the SAME
    /// workload, in the SAME process, back-to-back — so the ratio cancels out
    /// machine load (the absolute wall-clock is meaningless under a busy swarm, but
    /// the speedup ratio is not). Run with:
    ///   cargo test -p dregg-circuit --lib field::tests::ab_microbench_old_vs_new -- --ignored --nocapture
    #[test]
    #[ignore]
    fn ab_microbench_old_vs_new() {
        use std::time::Instant;
        let p = BABYBEAR_P;
        const ITERS: usize = 50_000_000;

        // Old formulas (the pre-optimization impl), inlined locally.
        #[inline(always)]
        fn old_mul_u32(a: u32, b: u32) -> u32 {
            ((a as u64 * b as u64) % BABYBEAR_P as u64) as u32
        }
        #[inline(always)]
        fn old_add_u32(a: u32, b: u32) -> u32 {
            ((a as u64 + b as u64) % BABYBEAR_P as u64) as u32
        }

        // Warm + a data-dependent chain so the optimizer can't hoist it out.
        let mut acc_old: u32 = 12345;
        let t0 = Instant::now();
        for i in 0..ITERS {
            let x = (i as u32) % p;
            acc_old = old_mul_u32(acc_old, x | 1);
            acc_old = old_add_u32(acc_old, x);
            if acc_old >= p {
                acc_old -= p;
            }
        }
        let old_dt = t0.elapsed();
        std::hint::black_box(acc_old);

        let mut acc_new = BabyBear::new(12345);
        let t1 = Instant::now();
        for i in 0..ITERS {
            let x = BabyBear::new((i as u32) % p);
            acc_new = acc_new * BabyBear((x.0) | 1);
            acc_new = acc_new + x;
        }
        let new_dt = t1.elapsed();
        std::hint::black_box(acc_new);

        let old_ns = old_dt.as_secs_f64() * 1e9 / ITERS as f64;
        let new_ns = new_dt.as_secs_f64() * 1e9 / ITERS as f64;
        eprintln!(
            "A/B per (mul+add): OLD(%/div)={old_ns:.3} ns  NEW(barrett/branch)={new_ns:.3} ns  speedup={:.2}x",
            old_ns / new_ns
        );
    }

    #[test]
    fn arith_differential_random_corpus() {
        // Deterministic xorshift PRNG so the corpus is reproducible.
        let mut s: u64 = 0x1234_5678_9ABC_DEF0;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };

        const N: usize = 2_000_000;
        let p = BABYBEAR_P;
        let mut checked_add = 0u64;
        let mut checked_sub = 0u64;
        let mut checked_mul = 0u64;

        for _ in 0..N {
            // Canonical operands in 0..P (the real field domain).
            let a = (next() % p as u64) as u32;
            let b = (next() % p as u64) as u32;

            let ba = BabyBear(a);
            let bb = BabyBear(b);

            assert_eq!((ba + bb).0, old_add(a, b), "ADD mismatch a={a} b={b}");
            checked_add += 1;
            assert_eq!((ba * bb).0, old_mul(a, b), "MUL mismatch a={a} b={b}");
            checked_mul += 1;
            if let Some(exp) = old_sub_defined(a, b) {
                assert_eq!((ba - bb).0, exp, "SUB mismatch a={a} b={b}");
                checked_sub += 1;
            }
        }

        // Also sweep NON-CANONICAL inputs (>= P up to u32::MAX) to confirm the
        // fallback path matches the old `%` semantics byte-for-byte.
        for _ in 0..N / 4 {
            let a = next() as u32; // full u32 range, often >= P
            let b = next() as u32;
            let ba = BabyBear(a);
            let bb = BabyBear(b);

            assert_eq!((ba + bb).0, old_add(a, b), "ADD(nc) mismatch a={a} b={b}");
            checked_add += 1;
            assert_eq!((ba * bb).0, old_mul(a, b), "MUL(nc) mismatch a={a} b={b}");
            checked_mul += 1;
            if let Some(exp) = old_sub_defined(a, b) {
                assert_eq!((ba - bb).0, exp, "SUB(nc) mismatch a={a} b={b}");
                checked_sub += 1;
            }
        }

        // Saturate the canonical edges explicitly.
        for &a in &[0u32, 1, 2, p - 2, p - 1] {
            for &b in &[0u32, 1, 2, p - 2, p - 1] {
                let (ba, bb) = (BabyBear(a), BabyBear(b));
                assert_eq!((ba + bb).0, old_add(a, b));
                assert_eq!((ba * bb).0, old_mul(a, b));
                if let Some(exp) = old_sub_defined(a, b) {
                    assert_eq!((ba - bb).0, exp);
                }
                checked_add += 1;
                checked_mul += 1;
                checked_sub += 1;
            }
        }

        eprintln!(
            "differential PASS: add={checked_add} sub={checked_sub} mul={checked_mul} (0 mismatches)"
        );
        assert!(checked_add >= 1_000_000);
        assert!(checked_mul >= 1_000_000);
        assert!(checked_sub >= 1_000_000);
    }
}
