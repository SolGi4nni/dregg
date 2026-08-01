//! BabyBear field — the verbatim arithmetic of `circuit/src/field.rs` /
//! `verifier-stark/src/stark_core/field.rs`, carried `no_std` and trimmed to the
//! surface the crypto floor needs (Poseidon2 + the byte/limb packing the BLAKE3
//! and nullifier portals use). Same prime `p = 2^31 - 2^27 + 1`, same canonical
//! reduction — so a digest computed here is byte-identical to one the
//! verifier-stark PD's STARK Merkle tree would compute.

#![allow(dead_code)]

use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// The BabyBear prime: p = 2^31 - 2^27 + 1 = 2013265921.
pub const BABYBEAR_P: u32 = (1 << 31) - (1 << 27) + 1;

/// A BabyBear field element: integers modulo p, stored canonically in [0, p-1].
#[derive(Clone, Copy)]
pub struct BabyBear(pub u32);

impl PartialEq for BabyBear {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.canonical_val() == other.canonical_val()
    }
}
impl Eq for BabyBear {}

impl BabyBear {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

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

    /// Create from a u64, reducing modulo p.
    #[inline]
    pub fn from_u64(val: u64) -> Self {
        Self((val % BABYBEAR_P as u64) as u32)
    }

    /// The canonical u32 representation.
    #[inline]
    pub fn as_u32(self) -> u32 {
        self.canonical_val()
    }

    /// Exponentiation by squaring (used by the Poseidon2 S-box x^7).
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

    /// **THE injective variable-length byte→felt preimage** — `BabyBear::bytes_to_lanes` from
    /// the circuit crate, the exact bridge `poseidon2::hash_bytes` uses for byte-oriented data
    /// (e.g. BLAKE3 commitments) entering the field domain.
    ///
    /// A four-lane base-`2^16` BYTE-COUNT header, then the bytes in little-endian `u16` pairs.
    /// Every lane is `< 2^16 = 65536 < p`, so `Self::new` never reduces one.
    ///
    /// ⚑ **This replaces `from_bytes_packed`, DELETED 2026-08-01 in both copies.** That map was
    /// 4-byte LE strides with the final partial chunk ZERO-FILLED and each chunk reduced `mod p`,
    /// and it was non-injective in two independent `O(1)` ways: `hash_bytes(b"foo") ==
    /// hash_bytes(b"foo\0")` (the padding is invisible and `hash_many`'s tag counts FELTS), and
    /// `[00,00,00,00]` vs `[01,00,00,78]` at equal length (`0x78000001 == p`). Lean authority and
    /// both exhibits: `metatheory/Dregg2/Circuit/BytesLanes.lean`.
    ///
    /// ⚠ This crate is `no_std`, is OUTSIDE the cargo workspace, and **does not build on the
    /// host at all** (`cargo check` here is `error: unwinding panics are not supported without
    /// std`; it cross-builds for `aarch64-unknown-linux-musl` only). So a `#[cfg(test)]` module
    /// in this crate can never go red and is not a gate — the existing one at `lib.rs:657` has
    /// the same property. The drift detector for this twin therefore lives where it can RUN:
    /// `the_out_of_workspace_crypto_floor_twin_has_not_drifted` in
    /// `circuit/tests/bytes_lanes_injective.rs` reads THIS FILE and fails if the retired packer
    /// reappears or the Lean-computed radix/header shape changes.
    pub fn bytes_to_lanes(bytes: &[u8]) -> alloc::vec::Vec<Self> {
        let mut result = alloc::vec::Vec::new();
        let mut rest = bytes.len() as u64;
        for _ in 0..4 {
            result.push(Self::new((rest % 65536) as u32));
            rest /= 65536;
        }
        let mut i = 0;
        while i < bytes.len() {
            let lo = bytes[i] as u32;
            let hi = if i + 1 < bytes.len() {
                bytes[i + 1] as u32
            } else {
                0
            };
            result.push(Self::new(lo + 256 * hi));
            i += 2;
        }
        result
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
