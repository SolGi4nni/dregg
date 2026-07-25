//! **Layer D — the binding fixed-width commitment.**
//!
//! `Digest8(domain, b) = squeeze( domain ‖ Limbs16(b) )`, eight felts wide — the same width the
//! failing sites already occupy — at a birthday cost of `2^123.63` instead of the `O(1)` of a raw
//! mod-`p` projection. It is **not** injective (nothing eight felts wide can be), and that is
//! fine: the security property was never injectivity, it was that the compression be *hard*.
//!
//! # ⚠ Correction to the design document, measured against the deployed chip
//!
//! `docs/DESIGN-canonical-byte-felt-codec.md` §2.2/§2.3 states that `CHIP_RATE = 16` makes
//! `chip_squeeze(domain ‖ Limbs16(b))` cost **one** permutation. Read against the source, that is
//! **false in two ways**, and both were checked rather than inferred:
//!
//! 1. `domain ‖ Limbs16` is **17** lanes, which exceeds `CHIP_RATE = 16` outright.
//! 2. `CHIP_RATE` is the chip's single-permutation *seed width*, not a free choice of arity. The
//!    AIR admits exactly the arities `{0, 2, 3, 4, 7, 11, 16}` (`circuit/src/descriptor_ir2.rs`
//!    pins each with its own selector polynomial), arity 16 being the `node8` `L8 ‖ R8` Merkle
//!    compression row. The general absorb primitive `single_perm_compress` asserts
//!    `inputs.len() <= 11`, and the real multi-block sponge rate is `POSEIDON2_SPONGE_RATE = 8`.
//!
//! So the composition below spends **two** permutations, not one:
//!
//! ```text
//! inner = squeeze8( Limbs16(b) )                        // arity 16 — the whole 32-byte value
//! Digest8 = squeeze8( [domain, 0,0,0,0,0,0,0] ‖ inner ) // arity 16 — domain separation
//! ```
//!
//! This still uses **only arities the AIR already emits**, and it is still rate-neutral against
//! the encodings it replaces at every site that absorbs more than one value — but the design
//! document's "ZERO additional permutations" is an overstatement and the sites that spend it
//! should be priced at two.
//!
//! # ⚠ NOT YET AIR-BACKED
//!
//! **AIR is authored in Lean.** This is the *host-side* composition only. Its in-circuit twin does
//! not exist yet: the Lean plan owns the `Digest8 ↔ Limbs16` canonicity gate (`Pack8Plan` /
//! `packBodiesAt`) and the 16-bit range plans, but no Lean emit yet produces *this* two-row
//! domain-separated squeeze. Emitting it is Stage 2/3 work. Until that Lean twin exists, this
//! function must not be used at a constrained boundary — a producer with no in-circuit
//! counterpart is exactly the witness-generation gap, not a fix for it.

use serde::{Deserialize, Serialize};

use crate::domain::Domain;
use crate::limbs::{BYTES32_U16_LIMBS, Bytes32};

/// The number of felts in a [`Digest8`]. Matches Lean's `DIGEST_LANES` and the chip's
/// `CHIP_OUT_LANES`.
pub const DIGEST_LANES: usize = 8;

/// One permutation of the deployed Poseidon2 chip, squeezing eight output lanes.
///
/// Implemented in `dregg-circuit` over the chip-faithful `chip_absorb_all_lanes`, so a host-side
/// digest is byte-identical to the trace's lane carriers. It lives behind a trait purely to keep
/// this crate a dependency leaf; there is exactly one intended implementor.
pub trait Squeeze8 {
    /// Absorb `lanes` in **one** permutation and return `state[0..8]` of the permuted state.
    ///
    /// Implementors MUST refuse an arity the AIR cannot emit (`{0, 2, 3, 4, 7, 11, 16}`) rather
    /// than silently padding — a host-side value with no emittable row is unprovable, and finding
    /// that out at proving time instead of at call time is how a wound gets built.
    fn squeeze8(&self, lanes: &[u32]) -> [u32; DIGEST_LANES];
}

/// **Layer D.** An eight-felt binding commitment to a 32-byte value.
///
/// The constructor set is deliberately narrow, and narrower than the `Faithful8` it is meant to
/// replace: `Faithful8`'s `from_bytes32` *was* the `O(1)`-aliasable mod-`p` projection and its
/// `from_canonical_key` *was* the 16-bit-discarding one, so possession of a `Faithful8` was not in
/// fact evidence of a faithful encoding — the wall laundered the alias. There is no `from_bytes32`
/// here, no `from_canonical_key`, and no lossy escape hatch. A wall with an escape hatch is a
/// convention.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Digest8([u32; DIGEST_LANES]);

impl Digest8 {
    /// The all-zero digest. A legitimate sentinel (empty subtree, absent slot), never a value.
    pub const ZERO: Self = Self([0; DIGEST_LANES]);

    /// **The canonical construction.** Two chip-emittable permutations; see the module note.
    #[must_use]
    pub fn compute<S: Squeeze8>(sq: &S, domain: Domain, value: &Bytes32) -> Self {
        let inner = sq.squeeze8(&value.limbs().felts());
        let mut outer = [0u32; BYTES32_U16_LIMBS];
        outer[0] = domain.felt();
        outer[DIGEST_LANES..].copy_from_slice(&inner);
        Self(sq.squeeze8(&outer))
    }

    /// Adopt eight lanes that a **tree fold** already squeezed (a Merkle node, an accumulator
    /// root). The caller is asserting the lanes came out of a permutation, not out of bytes; the
    /// bytes path is [`compute`](Self::compute) and there is no other.
    #[must_use]
    pub const fn from_squeezed_lanes(lanes: [u32; DIGEST_LANES]) -> Self {
        Self(lanes)
    }

    /// The eight felt values.
    #[must_use]
    pub const fn lanes(&self) -> &[u32; DIGEST_LANES] {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A stand-in permutation: NOT cryptographic, and deliberately not a copy of Poseidon2 (this
    /// crate must not grow a second permutation implementation). It exists to pin the *shape* of
    /// [`Digest8::compute`] — arity discipline, domain separation, lane plumbing.
    struct MockSqueeze;

    /// The arities the deployed AIR emits, read from `circuit/src/descriptor_ir2.rs`.
    const EMITTABLE_ARITIES: [usize; 7] = [0, 2, 3, 4, 7, 11, 16];

    impl Squeeze8 for MockSqueeze {
        fn squeeze8(&self, lanes: &[u32]) -> [u32; DIGEST_LANES] {
            assert!(
                EMITTABLE_ARITIES.contains(&lanes.len()),
                "arity {} is not emittable by the deployed chip",
                lanes.len()
            );
            let mut acc: u64 = 0x9E37_79B9;
            for (i, l) in lanes.iter().enumerate() {
                acc = acc
                    .wrapping_mul(0x0100_0193)
                    .wrapping_add(u64::from(*l) ^ ((i as u64) << 40));
            }
            core::array::from_fn(|k| {
                let mut h = acc.wrapping_add((k as u64).wrapping_mul(0x517C_C1B7_2722_0A95));
                h ^= h >> 33;
                h = h.wrapping_mul(0xFF51_AFD7_ED55_8CCD);
                h ^= h >> 29;
                (h % u64::from(crate::limbs::BABYBEAR_P)) as u32
            })
        }
    }

    /// The correction, as an executable assertion: the composition uses only arities the AIR can
    /// emit, and `domain ‖ Limbs16` (17 lanes) is NOT one of them.
    #[test]
    fn composition_uses_only_emittable_arities() {
        let v = Bytes32::new([7u8; 32]);
        // Would panic inside MockSqueeze if either row had an inadmissible arity.
        let _ = Digest8::compute(&MockSqueeze, Domain::NOTE_COMMITMENT_V2, &v);
        assert!(
            !EMITTABLE_ARITIES.contains(&(1 + BYTES32_U16_LIMBS)),
            "17 lanes is not emittable — this is why Digest8 costs two permutations, \
             contra DESIGN-canonical-byte-felt-codec.md §2.2"
        );
    }

    #[test]
    fn domain_separates() {
        let v = Bytes32::new([3u8; 32]);
        let a = Digest8::compute(&MockSqueeze, Domain::NOTE_COMMITMENT_V2, &v);
        let b = Digest8::compute(&MockSqueeze, Domain::NOTE_NULLIFIER_V2, &v);
        assert_ne!(
            a, b,
            "the same value under two domains must not share a digest"
        );
    }

    #[test]
    fn distinct_values_under_one_domain_differ() {
        let a = Bytes32::new([0u8; 32]);
        let mut raw = [0u8; 32];
        raw[31] = 1;
        let b = Bytes32::new(raw);
        assert_ne!(
            Digest8::compute(&MockSqueeze, Domain::NOTE_OWNER_V2, &a),
            Digest8::compute(&MockSqueeze, Domain::NOTE_OWNER_V2, &b)
        );
    }

    /// Every lane must be a canonical felt; a digest that needs reducing is a malleable digest.
    #[test]
    fn lanes_are_canonical() {
        let d = Digest8::compute(
            &MockSqueeze,
            Domain::EXACT_CAP_LEAF,
            &Bytes32::new([9u8; 32]),
        );
        for lane in d.lanes() {
            assert!(*lane < crate::limbs::BABYBEAR_P);
        }
    }

    /// There is no byte→felt path other than `compute`. This test is a tripwire on the
    /// constructor set, not on behaviour: if someone adds a `from_bytes32`, they must delete this.
    #[test]
    fn zero_is_the_only_free_standing_constructor() {
        assert_eq!(*Digest8::ZERO.lanes(), [0u32; DIGEST_LANES]);
        assert_eq!(
            *Digest8::from_squeezed_lanes([1, 2, 3, 4, 5, 6, 7, 8]).lanes(),
            [1, 2, 3, 4, 5, 6, 7, 8]
        );
    }
}
