//! # `Faithful8` — the faithful-commitment TYPE WALL.
//!
//! `docs/FAITHFUL-COMMITMENT-LAW.md`: every 32-byte component that flows into
//! the deployed state commitment binds its SOURCE at the system's own soundness
//! strength (~124-bit, the 8-felt encoding) — never a lossy 1-felt projection.
//!
//! The insidious failure mode the law names: **a bare `BabyBear` limb carries no
//! evidence of faithful-vs-degraded.** A faithful 8-felt binding and a degraded
//! ~31-bit Horner fold are the same type (`[BabyBear; 8]` / `BabyBear`), so a
//! lossy fold once slid into the commitment silently and was found only by a
//! bit-audit months later. The ast-grep gate (`scripts/check-no-degraded-felt.sh`)
//! catches the *pattern* in the three known producers; THIS newtype is the
//! *type-level* wall: a commitment-bearing octet sink takes `Faithful8`, and a
//! `Faithful8` can only be built through a named faithful constructor — so a
//! degraded felt in a commitment position is a **compile error**, everywhere,
//! including files the gate has never heard of.
//!
//! ## The constructor discipline
//!
//! The inner `[BabyBear; 8]` is **private**. The only ways in:
//!
//! * [`Faithful8::from_bytes32`] — the canonical full-32-byte limb split
//!   ([`crate::effect_vm::bytes32_to_8_limbs`]): 8 × 4-byte little-endian limbs,
//!   ~124-bit binding of the source bytes.
//! * the **tree roots** — the cap/heap/fields sorted-Poseidon2 `node8` trees
//!   return `Faithful8` directly from their root fold
//!   ([`crate::cap_root::compute_capability_root_with_tombstones`],
//!   [`crate::heap_root::compute_canonical_heap_root_8`],
//!   [`crate::heap_root::CanonicalHeapTree8::root8`], …); internally they use
//!   the crate-private [`Faithful8::from_root8`].
//! * the **wire-commit chain** — [`Faithful8::from_wire_commit`] /
//!   [`Faithful8::from_wire_commit_chip`], the chained 8-felt rotated state
//!   commitment (`poseidon2::wire_commit_8` / `wire_commit_8_chip`).
//! * [`Faithful8::from_canonical_key`] — the 30-bit canonical key-commit octet
//!   (the pubkey8 lane). NOT a 4-byte limb split: the packing is the KEY_COMMIT
//!   canonical form (`dregg_commit::typed::canonical_32_to_felts_8` /
//!   `dregg_cell::commitment::canonical_to_babybear_pi` — 8+8+8+6 = 30 bits per
//!   limb, 240 bits total, faithful).
//! * [`Faithful8::ZERO`] — the all-zero sentinel (absent carrier material, the
//!   deployed `vk_hash == [0; 8]` revoke convention). Zero is not a projection
//!   of anything; it is the committed "nothing here" value.
//! * [`Faithful8::from_lossy_31bit_DANGER`] — the **greppable escape hatch** for
//!   the named, allowlisted residuals (today: exactly the `fields[0..7]` r3..r10
//!   Horner folds, pending the v13 epoch). Every call site is a v13 burn-down
//!   list entry. Adding one without updating
//!   `docs/FAITHFUL-COMMITMENT-LAW.md` is a review-time violation.
//!
//! Reading OUT is unrestricted (`Deref<Target = [BabyBear; 8]>`, [`Faithful8::limbs`],
//! `From<Faithful8> for [BabyBear; 8]`): the wall polices construction, not
//! inspection — that is what stops the cascade at module boundaries.
//!
//! ## The tripwire
//!
//! A bare `[BabyBear; 8]` cannot enter a `Faithful8` sink without naming a
//! constructor — the inner field is private and there is deliberately no
//! `From<[BabyBear; 8]>`:
//!
//! ```compile_fail
//! use dregg_circuit::faithful8::Faithful8;
//! use dregg_circuit::field::BabyBear;
//! // A degraded fold wearing an 8-wide coat — REFUSED at compile time:
//! let degraded_lane0 = BabyBear::new(0x1234);
//! let mut coat = [BabyBear::ZERO; 8];
//! coat[0] = degraded_lane0;
//! let smuggled: Faithful8 = Faithful8(coat); // private field — no constructor named
//! ```
//!
//! ```compile_fail
//! use dregg_circuit::faithful8::Faithful8;
//! use dregg_circuit::field::BabyBear;
//! let bare = [BabyBear::ONE; 8];
//! let smuggled: Faithful8 = bare.into(); // no From<[BabyBear; 8]> — the wall
//! ```

use crate::field::BabyBear;

/// A **faithful 8-felt commitment octet** (~124-bit binding of its source).
///
/// See the module docs for the constructor discipline. The inner array is
/// private on purpose: possession of a `Faithful8` is evidence the value came
/// from a faithful encoder (or a NAMED, greppable `_DANGER` residual site).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Faithful8([BabyBear; 8]);

impl Faithful8 {
    /// The all-zero sentinel octet: absent carrier material (child_vk /
    /// contract_hash on a non-factory / non-hatchery block), the deployed
    /// `vk_hash == [0; 8]` revoke convention. Committed "nothing here" — not a
    /// projection of any 32-byte source.
    pub const ZERO: Self = Self([BabyBear::ZERO; 8]);

    /// The canonical full-32-byte limb split ([`crate::effect_vm::bytes32_to_8_limbs`]):
    /// limb `i` carries bytes `[4i..4i+4]` little-endian, reduced mod `p`. The
    /// faithful ~124-bit binding of `b` — THE constructor for hash-rooted octets
    /// (blake3 digests, VK hashes, contract hashes, …).
    #[inline]
    pub fn from_bytes32(b: &[u8; 32]) -> Self {
        Self(crate::effect_vm::bytes32_to_8_limbs(b))
    }

    /// Crate-private: wrap a `node8` tree-root / chip-digest fold that is
    /// faithful BY CONSTRUCTION (every lane a genuine output lane of the
    /// arity-16 `node8` / rate-8 chip permutation). Only the tree/commit
    /// modules inside `dregg-circuit` may call this — external producers go
    /// through the public constructors.
    #[inline]
    pub(crate) const fn from_root8(limbs: [BabyBear; 8]) -> Self {
        Self(limbs)
    }

    /// The chained 8-felt rotated state commitment over `(pre_limbs, iroot)` —
    /// [`crate::poseidon2::wire_commit_8`] (the plain chain, Lean `wireCommitR8`).
    #[inline]
    pub fn from_wire_commit(pre_limbs: &[BabyBear], iroot: BabyBear) -> Self {
        Self(crate::poseidon2::wire_commit_8(pre_limbs, iroot))
    }

    /// The chained CHIP-FAITHFUL 8-felt rotated state commitment —
    /// [`crate::poseidon2::wire_commit_8_chip`], the byte-twin of the deployed
    /// wide trace's `fill_wide_block` absorption (`chip_absorb_all_lanes`).
    #[inline]
    pub fn from_wire_commit_chip(pre_limbs: &[BabyBear], iroot: BabyBear) -> Self {
        Self(crate::poseidon2::wire_commit_8_chip(pre_limbs, iroot))
    }

    /// The 30-bit canonical KEY-COMMIT octet (the `pubkey8` carrier lane): 8
    /// limbs of `8+8+8+6 = 30` bits each over the canonical 32-byte key — 240
    /// bits, faithful. The packing is owned by
    /// `dregg_commit::typed::canonical_32_to_felts_8` (byte-identical twin:
    /// `dregg_cell::commitment::canonical_to_babybear_pi`); this constructor
    /// takes its output and NAMES the lane so the wall stays greppable.
    #[inline]
    pub fn from_canonical_key(limbs: [BabyBear; 8]) -> Self {
        Self(limbs)
    }

    /// The v13 FIELDS-OCTET projection ([`crate::effect_vm::field_limbs8`]): the
    /// faithful ~124-bit 8-lane split of a 32-byte flat-record field value, lane
    /// 0 = the u64-lane `lo32`, lane 1 = the u64-lane `hi32`, lanes 2..7 = the
    /// remaining bytes little-endian (see the `field_limbs8` doc for the encoding
    /// audit). THE constructor for the `fields[0..7]` octets — it REPLACES the
    /// former eight ~31-bit `fold_bytes32_to_bb` Horner folds that rode one
    /// `from_lossy_31bit_DANGER` octet (the v13 burn-down, closing the LAST
    /// degraded-felt residual). Each field's lane 0 rides its existing welded
    /// limb `4 + i`; lanes 1..7 ride the completion lanes `112 + 7·i .. +6`.
    #[inline]
    pub fn from_field_limbs8(b: &[u8; 32]) -> Self {
        Self(crate::effect_vm::field_limbs8(b))
    }

    /// **THE GREPPABLE ESCAPE HATCH** for the NAMED degraded residuals
    /// (`docs/FAITHFUL-COMMITMENT-LAW.md` — the v13 burn-down list). A call
    /// site of this constructor is an admission: these 8 limbs do NOT each
    /// bind a faithful source (e.g. eight independent ~31-bit Horner folds
    /// riding in one octet). `reason` must name the residual and its closure
    /// epoch. Every call site is reviewed against the law doc's allowlist.
    #[allow(non_snake_case)]
    #[inline]
    pub fn from_lossy_31bit_DANGER(reason: &'static str, limbs: [BabyBear; 8]) -> Self {
        debug_assert!(
            !reason.is_empty(),
            "from_lossy_31bit_DANGER: a named residual needs a non-empty reason"
        );
        Self(limbs)
    }

    /// The 8 lanes, by value. Reading out is unrestricted — the wall polices
    /// construction, not inspection.
    #[inline]
    pub fn limbs(&self) -> [BabyBear; 8] {
        self.0
    }

    /// Write the octet CONTIGUOUSLY into a pre-limbs / row slice at `base`
    /// (lane `i` → `slice[base + i]`). A typed commitment SINK: only a
    /// `Faithful8` can be written through it.
    #[inline]
    pub fn write_octet(&self, limbs: &mut [BabyBear], base: usize) {
        limbs[base..base + 8].copy_from_slice(&self.0);
    }

    /// Write the octet SCATTERED: lane `i` → `slice[positions[i]]` (the rotated
    /// pre-limb groups whose completion lanes live in non-contiguous headroom,
    /// e.g. cap_root lane 0 at limb 25 ‖ lanes 1..7 at limbs 51..57). A typed
    /// commitment SINK.
    #[inline]
    pub fn write_lanes(&self, limbs: &mut [BabyBear], positions: [usize; 8]) {
        for (lane, &pos) in self.0.iter().zip(positions.iter()) {
            limbs[pos] = *lane;
        }
    }
}

/// Read-only access to the lanes (indexing, iteration, slicing, `&Faithful8 →
/// &[BabyBear; 8]` deref coercion). This is what stops the consumer cascade at
/// module boundaries: a `root8()[0]` / `for lane in &root8` site compiles
/// unchanged.
impl std::ops::Deref for Faithful8 {
    type Target = [BabyBear; 8];
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Unwrap at a module boundary (`let bare: [BabyBear; 8] = f8.into()`).
impl From<Faithful8> for [BabyBear; 8] {
    #[inline]
    fn from(f: Faithful8) -> Self {
        f.0
    }
}

impl AsRef<[BabyBear; 8]> for Faithful8 {
    #[inline]
    fn as_ref(&self) -> &[BabyBear; 8] {
        &self.0
    }
}

impl AsRef<[BabyBear]> for Faithful8 {
    #[inline]
    fn as_ref(&self) -> &[BabyBear] {
        &self.0
    }
}

/// `assert_eq!(faithful, bare_array)` in the differentials without unwrap noise.
impl PartialEq<[BabyBear; 8]> for Faithful8 {
    #[inline]
    fn eq(&self, other: &[BabyBear; 8]) -> bool {
        &self.0 == other
    }
}

impl PartialEq<Faithful8> for [BabyBear; 8] {
    #[inline]
    fn eq(&self, other: &Faithful8) -> bool {
        self == &other.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn from_bytes32_matches_the_canonical_limb_split() {
        let mut b = [0u8; 32];
        for (i, byte) in b.iter_mut().enumerate() {
            *byte = i as u8;
        }
        let f = Faithful8::from_bytes32(&b);
        assert_eq!(f.limbs(), crate::effect_vm::bytes32_to_8_limbs(&b));
        // Deref indexing + the cross-type PartialEq both see the same lanes.
        assert_eq!(f[0], crate::effect_vm::bytes32_to_8_limbs(&b)[0]);
        assert_eq!(f, crate::effect_vm::bytes32_to_8_limbs(&b));
    }

    #[test]
    fn write_octet_and_write_lanes_place_every_lane() {
        let mut b = [0u8; 32];
        b[0] = 1;
        b[31] = 7;
        let f = Faithful8::from_bytes32(&b);
        let mut buf = [BabyBear::ZERO; 16];
        f.write_octet(&mut buf, 4);
        assert_eq!(&buf[4..12], &f.limbs());
        let mut buf2 = vec![BabyBear::ZERO; 60];
        let pos = [25usize, 51, 52, 53, 54, 55, 56, 57];
        f.write_lanes(&mut buf2, pos);
        for (lane, &p) in f.limbs().iter().zip(pos.iter()) {
            assert_eq!(buf2[p], *lane);
        }
    }

    #[test]
    fn zero_sentinel_is_all_zero() {
        assert_eq!(Faithful8::ZERO.limbs(), [BabyBear::ZERO; 8]);
    }
}
