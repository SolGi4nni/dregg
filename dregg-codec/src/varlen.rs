//! **Layer L at VARIABLE length** — the injective preimage a byte-sponge absorbs.
//!
//! [`Limbs16`](crate::Limbs16) covers the fixed 32-byte case. This module covers the other one:
//! an arbitrary-length byte string that has to enter a Poseidon2 sponge without two distinct
//! strings ever landing on the same felt sequence.
//!
//! ```text
//! bytes_to_lanes(bs) = len_lanes(bs.len())  ‖  u16 pairs of bs, little-endian
//! ```
//!
//! * **`len_lanes(n)`** — the BYTE count as four base-`2^16` digits. Four, not one, so the header
//!   is total to `2^64` bytes rather than correct-in-practice.
//! * **the pairs** — `⌈n/2⌉` lanes, each `b[2i] + 256·b[2i+1]`, the final lane's high byte zero
//!   when `n` is odd. Every lane is `< 2^16 ≪ p`, so **no lane ever reduces**.
//!
//! [`lanes_to_bytes`] is TOTAL and is a LEFT INVERSE, so the map is injective — not a hash bound,
//! not a birthday bound.
//!
//! # The map this replaces, and both of its `O(1)` collisions
//!
//! `dregg_circuit::field::BabyBear::from_bytes_packed` (DELETED 2026-08-01) walked the input in
//! 4-byte strides, zero-filling the final partial chunk, and reduced each chunk `mod p`. Its
//! consumer `hash_bytes` tagged the sponge with the FELT count. Two free collisions followed:
//!
//! 1. **the NUL-append.** `hash_bytes(b"foo") == hash_bytes(b"foo\0")`, and
//!    `hash_bytes(b"f") == hash_bytes(b"f\0\0\0")` — the padding is invisible and the felt count
//!    does not move. Cost: one byte.
//! 2. **the mod-`p` alias, AT EQUAL LENGTH.** `p = 2013265921 = 0x78000001 < 2^32`, so the four
//!    bytes `01 00 00 78` pack to exactly `p` and reduce to `0`, colliding with `00 00 00 00`.
//!    `2^32 − p = 2281701375`, i.e. **53.1%** of `u32` chunks have a `+p` sibling. No length tag
//!    of any kind separates these, which is why the repair had to change the RADIX.
//!
//! # ⚠ The residual, with its bound, because this closes one defect and not the other
//!
//! An injective preimage says nothing about the SQUEEZE. `dregg_circuit::poseidon2::hash_bytes`
//! still returns ONE felt, and `log2(p) = 30.906891`, so an unstructured collision search costs
//! the birthday bound `2^15.4534` ≈ 44,900 evaluations — milliseconds.
//! `docs/DESIGN-canonical-byte-felt-codec.md` §2.3 bans that shape by name (`Digest1`). Prefer
//! `hash_bytes_8` wherever the sink can hold eight felts (`2^123.63`); where it cannot — the
//! `HeapLeaf.value : BabyBear` field and the `MapOp` value width — the fix is a constraint change
//! owned by the value-widening campaign, and **no preimage repair reaches it.**
//!
//! # Lean authority
//!
//! `metatheory/Dregg2/Circuit/BytesLanes.lean`:
//!
//! * `lanesToBytes_bytesToLanes` — a total decoder that is a LEFT INVERSE on every byte string
//!   shorter than `2^64`,
//! * `bytesToLanes_injective` — its corollary,
//! * `legacy_admits_the_nul_append` / `legacy_admits_the_modP_alias` — both old collisions
//!   exhibited over a Lean twin of the deleted packer,
//! * `nonet_rejects_the_nul_append` / `nonet_rejects_the_modP_alias` — the same pairs separating.
//!
//! all `#assert_axioms`-clean. ⚑ **And the honest half:** those are theorems about the LEAN
//! encoder. There is no formal semantics of Rust and this body is not extracted from the Lean, so
//! it is pinned to the spec by Lean-COMPUTED KAT vectors plus a round-trip sweep
//! (`circuit/tests/bytes_lanes_injective.rs`) — a strictly stronger claim than the deleted packer
//! could make and a strictly weaker one than "verified". Say it at that resolution.

/// Lanes in the byte-count header: four base-`2^16` digits, total to `2^64` bytes.
///
/// Mirrors Lean `lenLanes`, whose `digitsN U16 4` is the same four digits.
pub const LEN_HEADER_LANES: usize = 4;

/// The lane radix, `2^16`. Every lane of [`bytes_to_lanes`] is strictly below it, and it is
/// strictly below [`BABYBEAR_P`](crate::limbs::BABYBEAR_P) — which is the entire reason no lane
/// reduces.
pub const LANE_RADIX: u32 = 1 << 16;

/// The byte length as four base-`2^16` digits, low digit first. Mirrors Lean `lenLanes`.
#[must_use]
pub fn len_lanes(n: u64) -> [u32; LEN_HEADER_LANES] {
    let mut out = [0u32; LEN_HEADER_LANES];
    let mut rest = n;
    for slot in &mut out {
        *slot = (rest % u64::from(LANE_RADIX)) as u32;
        rest /= u64::from(LANE_RADIX);
    }
    out
}

/// **THE ENCODER.** Byte-count header, then the little-endian `u16` pairs.
///
/// Mirrors Lean `bytesToLanes`. Injective: [`lanes_to_bytes`] is a left inverse.
#[must_use]
pub fn bytes_to_lanes(data: &[u8]) -> Vec<u32> {
    let mut out = Vec::with_capacity(LEN_HEADER_LANES + data.len().div_ceil(2));
    out.extend_from_slice(&len_lanes(data.len() as u64));
    for pair in data.chunks(2) {
        let lo = u32::from(pair[0]);
        let hi = pair.get(1).map_or(0, |b| u32::from(*b));
        out.push(lo + 256 * hi);
    }
    out
}

/// **THE DECODER.** Total on every lane vector — a vector no encoder produced is read modulo the
/// radix and truncated to the header's length, which is what makes this a function and not a
/// partial one. Mirrors Lean `lanesToBytes`.
#[must_use]
pub fn lanes_to_bytes(lanes: &[u32]) -> Vec<u8> {
    let header = lanes.iter().take(LEN_HEADER_LANES);
    let mut len: u64 = 0;
    for (i, digit) in header.enumerate() {
        len = len.wrapping_add(
            u64::from(*digit % LANE_RADIX).wrapping_mul(u64::from(LANE_RADIX).pow(i as u32)),
        );
    }
    let body = lanes.iter().skip(LEN_HEADER_LANES);
    let mut out: Vec<u8> = Vec::new();
    for lane in body {
        out.push((lane % 256) as u8);
        out.push((lane / 256 % 256) as u8);
    }
    let keep = usize::try_from(len).unwrap_or(usize::MAX).min(out.len());
    out.truncate(keep);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::limbs::BABYBEAR_P;

    /// The inequality the whole design rests on: a lane can never need reducing.
    ///
    /// ⚑ The `LANE_RADIX < BABYBEAR_P` half is two constants, so it is a BUILD obligation and is
    /// discharged as one below; what remains here is the part a running check decides — that the
    /// encoder's actual output stays inside the radix over a real range of inputs.
    const NO_LANE_EVER_REDUCES: () = assert!(
        LANE_RADIX < BABYBEAR_P,
        "a lane radix at or above the modulus makes the varlen encoding a mod-p map"
    );
    const _: () = NO_LANE_EVER_REDUCES;

    /// …and the encoder's ACTUAL output honours it, over a real range of payload lengths.
    #[test]
    fn no_lane_ever_reduces_over_real_payloads() {
        for len in 0..200usize {
            let data: Vec<u8> = (0..len)
                .map(|i| (i as u8).wrapping_mul(37) ^ 0xA5)
                .collect();
            for lane in bytes_to_lanes(&data) {
                assert!(lane < LANE_RADIX, "lane {lane} escaped the radix");
                assert!(lane < BABYBEAR_P);
            }
        }
    }

    /// ANTI-VACUITY: the VALUE comes back. A scrambling "repair" passes a difference-only test and
    /// fails this one.
    #[test]
    fn round_trip_returns_the_value() {
        for len in 0..300usize {
            let data: Vec<u8> = (0..len)
                .map(|i| (i as u8).wrapping_mul(97).wrapping_add(13))
                .collect();
            assert_eq!(lanes_to_bytes(&bytes_to_lanes(&data)), data, "len {len}");
        }
    }

    /// The NUL-append separates — and specifically in the HEADER, not by luck in the tail.
    #[test]
    fn nul_append_separates_in_the_header() {
        for len in 0..64usize {
            let base: Vec<u8> = (0..len).map(|i| (i as u8) ^ 0x5C).collect();
            for pad in 1..=4usize {
                let mut padded = base.clone();
                padded.extend(std::iter::repeat_n(0u8, pad));
                let a = bytes_to_lanes(&base);
                let b = bytes_to_lanes(&padded);
                assert_ne!(a, b, "len {len} + {pad} NULs collided");
                assert_ne!(a[0..LEN_HEADER_LANES], b[0..LEN_HEADER_LANES]);
            }
        }
    }

    /// The mod-`p` alias that the deleted packer admitted AT EQUAL LENGTH.
    #[test]
    fn the_equal_length_mod_p_alias_separates() {
        let zero4 = [0u8, 0, 0, 0];
        // 0x78000001 little-endian == BABYBEAR_P.
        let alias4 = [1u8, 0, 0, 0x78];
        assert_eq!(u32::from_le_bytes(alias4), BABYBEAR_P);
        assert_eq!(zero4.len(), alias4.len());
        assert_ne!(bytes_to_lanes(&zero4), bytes_to_lanes(&alias4));
    }

    /// A length past `2^16` needs the second header digit; a one-lane header would have been an
    /// aliasing bug of its own.
    #[test]
    fn the_header_is_four_digits_wide() {
        assert_eq!(len_lanes(70_000), [4464, 1, 0, 0]);
        assert_eq!(len_lanes(0), [0, 0, 0, 0]);
        assert_eq!(len_lanes(u64::from(LANE_RADIX) - 1), [65535, 0, 0, 0]);
    }
}
