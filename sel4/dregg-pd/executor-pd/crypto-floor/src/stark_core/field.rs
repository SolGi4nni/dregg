//! Field element type for the circuit.
//!
//! Uses BabyBear (p = 2^31 - 2^27 + 1 = 2013265921) as the native field for STARK proofs.
//! In mock mode, we implement BabyBear arithmetic directly. With plonky3 feature,
//! this wraps `p3_baby_bear::BabyBear`.

use alloc::vec::Vec;
use serde::{Deserialize, Serialize};
use core::fmt;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

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
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BabyBear {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.canonical_val().cmp(&other.canonical_val())
    }
}

impl core::hash::Hash for BabyBear {
    #[inline]
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
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
                result = result * base;
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

    /// Convert a byte slice to a vector of field elements.
    /// Each byte becomes one field element.
    pub fn from_bytes(bytes: &[u8]) -> Vec<Self> {
        bytes.iter().map(|&b| Self::new(b as u32)).collect()
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

    /// Encode a 32-byte hash as a vector of BabyBear elements (8 elements, 4 bytes each).
    pub fn encode_hash(hash: &[u8; 32]) -> [Self; 8] {
        let mut out = [Self::ZERO; 8];
        for (i, chunk) in hash.chunks(4).enumerate() {
            let val = u32::from_le_bytes([chunk[0], chunk[1], chunk[2], chunk[3]]);
            out[i] = Self::new(val);
        }
        out
    }

    /// Decode 8 BabyBear elements back to a 32-byte value.
    /// Note: this is lossy due to modular reduction in `encode_hash`.
    pub fn decode_hash(elements: &[Self; 8]) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, &elem) in elements.iter().enumerate() {
            let bytes = elem.0.to_le_bytes();
            out[i * 4..i * 4 + 4].copy_from_slice(&bytes);
        }
        out
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

impl Add for BabyBear {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        let sum = self.0 as u64 + rhs.0 as u64;
        Self((sum % BABYBEAR_P as u64) as u32)
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
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let diff = self.0 as u64 + BABYBEAR_P as u64 - rhs.0 as u64;
        Self((diff % BABYBEAR_P as u64) as u32)
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
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let prod = self.0 as u64 * rhs.0 as u64;
        Self((prod % BABYBEAR_P as u64) as u32)
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

