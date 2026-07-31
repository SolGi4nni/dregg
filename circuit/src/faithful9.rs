//! # `Faithful9` — the fields-octet wall that is actually an INJECTION.
//!
//! [`crate::faithful8::Faithful8`] guards **width** (1 felt vs 8) and its own module docs say
//! plainly that it guards nothing else: `from_bytes32` is `O(1)`-aliasable, `from_canonical_key`
//! discards 16 source bits, and `from_field_limbs8` rides an 8-lane scheme that **cannot** be
//! injective — `p = 2013265921`, `log₂ p = 30.907`, so eight lanes carry 247.26 bits against a
//! 32-byte field's 256. Pigeonhole, before you read a line of code. A `Faithful8` therefore
//! LAUNDERS: a sink cannot tell an aliased octet from a hard one.
//!
//! **`Faithful9` is the one that can say the other thing.** Its single constructor is the
//! nine-lane fields encoder [`crate::effect_vm::field_limbs9`], whose Lean authority
//! `metatheory/Dregg2/Circuit/FieldLanes9.lean` carries
//!
//! * `lanes9ToField_fieldToLanes9` — a total decoder that is a LEFT INVERSE on every 32-byte value,
//! * `fieldToLanes9_injective` — `Function.Injective fieldToLanes9`, its corollary,
//! * `nine_lanes_is_the_minimum` — `P^8 < 2^256 ≤ P^9`,
//!
//! all `#assert_axioms`-clean. Not a hash bound, not a birthday bound: an explicit bijection onto
//! its image.
//!
//! ⚑ **AND THE HONEST HALF OF THAT SENTENCE.** Those are theorems about the LEAN encoder. There is
//! no formal semantics of Rust and this crate's `field_limbs9` is not extracted from the Lean, so
//! possession of a `Faithful9` is evidence that the value came from a Rust encoder pinned to a
//! verified spec **by Lean-computed KAT vectors and a round-trip sweep**
//! (`circuit/tests/field_lanes9_injective.rs`) — not from a verified encoder. That is a strictly
//! stronger claim than any `Faithful8` constructor can make and a strictly weaker one than
//! "verified". Say it at that resolution.
//!
//! ## The constructor discipline
//!
//! The inner `[BabyBear; 9]` is private and there is **exactly one way in**:
//! [`Faithful9::from_field_lanes9`]. There is deliberately **no** `From<[BabyBear; 9]>`, no
//! `from_lanes`, and **no `_DANGER` escape hatch** — `Faithful8`'s own docs record that "a wall with
//! an escape hatch is a convention", and its `from_lossy_31bit_DANGER` is why that sentence had to
//! be written. Do not add one here. If a caller has nine bare felts and no 32-byte source, it does
//! not have a `Faithful9`; it has nine felts.
//!
//! Reading OUT is unrestricted (`Deref<Target = [BabyBear; 9]>`, [`Faithful9::lanes`],
//! `From<Faithful9> for [BabyBear; 9]`): the wall polices construction, not inspection.
//!
//! ## The tripwire
//!
//! ```compile_fail
//! use dregg_circuit::faithful9::Faithful9;
//! use dregg_circuit::field::BabyBear;
//! let bare = [BabyBear::ONE; 9];
//! let smuggled: Faithful9 = Faithful9(bare); // private field — no constructor named
//! ```
//!
//! ```compile_fail
//! use dregg_circuit::faithful9::Faithful9;
//! use dregg_circuit::field::BabyBear;
//! let bare = [BabyBear::ONE; 9];
//! let smuggled: Faithful9 = bare.into(); // no From<[BabyBear; 9]> — the wall
//! ```

use crate::field::BabyBear;

/// A **9-felt fields-octet lane vector**, built only by the injective encoder.
///
/// Unlike [`crate::faithful8::Faithful8`], possession of this type is evidence about BINDING and
/// not merely width: the encoding it wraps has a machine-checked left inverse in Lean
/// (`lanes9ToField_fieldToLanes9`) and is therefore injective (`fieldToLanes9_injective`) — two
/// distinct 32-byte field values can never share a lane vector. The Rust body is pinned to that
/// spec by KAT + round-trip, not extracted from it; see the module docs.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Faithful9([BabyBear; 9]);

impl Faithful9 {
    /// **THE ONLY CONSTRUCTOR.** The nine-lane fields encoding of a 32-byte flat-record field value
    /// ([`crate::effect_vm::field_limbs9`], Lean `fieldToLanes9`).
    ///
    /// Lanes 0/1 are byte-identically the kernel u64 lane (`BE(b[28..32]) % p`, `BE(b[24..28]) % p`)
    /// — the deployed ABI the escrow / discharge / vault welds read, unchanged. Lanes 2..8 are the
    /// seven base-`2^28` digits of `W = ofDigits 256 (b[0..24] ++ [q₀ + 4·q₁])`, which is what makes
    /// the whole vector injective: the quotients lane 0/1's `mod p` discards are carried in lane 8's
    /// digit, and the 24 bytes the pinned pair says nothing about are carried outright.
    ///
    /// The inverse is [`crate::effect_vm::field_from_lanes9`].
    #[inline]
    pub fn from_field_lanes9(b: &[u8; 32]) -> Self {
        Self(crate::effect_vm::field_limbs9(b))
    }

    /// The 32-byte value this vector encodes. Total, and the exact inverse of
    /// [`Faithful9::from_field_lanes9`] — a `Faithful9` can always be read back, which is precisely
    /// what no `Faithful8` constructor supports.
    #[inline]
    pub fn to_field_bytes(&self) -> [u8; 32] {
        crate::effect_vm::field_from_lanes9(&self.0)
    }

    /// The 9 lanes, by value. Reading out is unrestricted.
    #[inline]
    pub fn lanes(&self) -> [BabyBear; 9] {
        self.0
    }

    /// Write the vector SCATTERED: lane `i` → `limbs[positions[i]]`.
    ///
    /// The nine-wide counterpart of `Faithful8::write_lanes`. The rotated pre-limb groups keep
    /// their completion lanes in non-contiguous headroom, so the sink takes an explicit index array
    /// rather than a base.
    #[inline]
    pub fn write_lanes(&self, limbs: &mut [BabyBear], positions: [usize; 9]) {
        for (lane, &pos) in self.0.iter().zip(positions.iter()) {
            limbs[pos] = *lane;
        }
    }

    /// Write the vector CONTIGUOUSLY into a pre-limbs / row slice at `base` (lane `i` →
    /// `limbs[base + i]`).
    #[inline]
    pub fn write_vector(&self, limbs: &mut [BabyBear], base: usize) {
        limbs[base..base + 9].copy_from_slice(&self.0);
    }
}

/// Read-only access to the lanes (indexing, iteration, slicing).
impl std::ops::Deref for Faithful9 {
    type Target = [BabyBear; 9];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Unwrap at a module boundary (`let bare: [BabyBear; 9] = f9.into()`).
impl From<Faithful9> for [BabyBear; 9] {
    #[inline]
    fn from(f: Faithful9) -> Self {
        f.0
    }
}

impl AsRef<[BabyBear; 9]> for Faithful9 {
    #[inline]
    fn as_ref(&self) -> &[BabyBear; 9] {
        &self.0
    }
}

impl AsRef<[BabyBear]> for Faithful9 {
    #[inline]
    fn as_ref(&self) -> &[BabyBear] {
        &self.0
    }
}

/// `assert_eq!(faithful, bare_array)` in the differentials without unwrap noise.
impl PartialEq<[BabyBear; 9]> for Faithful9 {
    #[inline]
    fn eq(&self, other: &[BabyBear; 9]) -> bool {
        &self.0 == other
    }
}

impl PartialEq<Faithful9> for [BabyBear; 9] {
    #[inline]
    fn eq(&self, other: &Faithful9) -> bool {
        self == &other.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_only_constructor_is_the_encoder_and_it_round_trips() {
        let mut b = [0u8; 32];
        for (i, byte) in b.iter_mut().enumerate() {
            *byte = (i as u8).wrapping_mul(37).wrapping_add(11);
        }
        let f = Faithful9::from_field_lanes9(&b);
        assert_eq!(f.lanes(), crate::effect_vm::field_limbs9(&b));
        // ANTI-VACUITY: the VALUE comes back, so a constructor that scrambled would fail here.
        assert_eq!(f.to_field_bytes(), b);
        assert_eq!(f[0], crate::effect_vm::field_limbs9(&b)[0]);
        assert_eq!(f, crate::effect_vm::field_limbs9(&b));
    }

    #[test]
    fn write_lanes_and_write_vector_place_every_lane() {
        let mut b = [0u8; 32];
        b[0] = 1;
        b[31] = 7;
        let f = Faithful9::from_field_lanes9(&b);

        let mut buf = [BabyBear::ZERO; 16];
        f.write_vector(&mut buf, 4);
        assert_eq!(&buf[4..13], &f.lanes());

        let mut buf2 = vec![BabyBear::ZERO; 64];
        let pos = [25usize, 51, 52, 53, 54, 55, 56, 57, 58];
        f.write_lanes(&mut buf2, pos);
        for (lane, &p) in f.lanes().iter().zip(pos.iter()) {
            assert_eq!(buf2[p], *lane);
        }
    }
}
