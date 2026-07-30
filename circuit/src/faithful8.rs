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
//! ## ⚠ WHAT THIS WALL DOES NOT GUARD — read before trusting a `Faithful8`
//!
//! It guards the **WIDTH** axis (1 felt vs 8) and it guards it well. Wound #23 is the natural
//! experiment: a 1-felt heap root sat *"three fields away from three siblings
//! (`nullifier_root`/`commitments_root`/`revoked_root`) that were already `Faithful8`"* — three
//! correct uses, one bare `BabyBear`, same struct, ~2^31 grind on the consensus anchor. The wall's
//! absence made #23 possible; its presence made the three siblings safe.
//!
//! But it has **no opinion whatsoever about whether those 8 felts are a HARD COMPRESSION or a
//! FREE-ALIAS PROJECTION**, and its own constructor list admits the failures:
//!
//! * [`Faithful8::from_bytes32`] **is** `bytes32_to_8_limbs` — family F1, `O(1)` aliasable for a
//!   directly-chosen preimage (`v` and `v + p` collide for 53.1% of 4-byte chunks).
//! * [`Faithful8::from_canonical_key`] **is** `canonical_32_to_felts_8` — family F2, 16 source
//!   bits discarded.
//! * [`Faithful8::from_field_limbs8`] **is** `field_limbs8` — family F3. ⚑ **This one was missing
//!   from the list**, and it is the constructor that feeds `fields[0..7]` — the only octet in the
//!   v9 commitment with no byte-exact companion, so it is the one where an alias reaches the signed
//!   anchor. Added 2026-07-30. It WAS `O(1)` aliasable exactly like F1; lanes 2..7 now carry a
//!   Poseidon2 image over an injective preimage, so the constructed alias is gone and the cost is
//!   the hash's. It is still not injective — the counting argument below applies to every 8-lane
//!   scheme regardless of what the lanes carry.
//!
//! ⚑ **THE COUNTING ARGUMENT, which subsumes every entry above.** `p = 2013265921`, so
//! `log2 p = 30.907` and eight lanes carry **247.26 bits** against a 32-byte field's **256**. No
//! 8-lane encoding of 32 bytes is injective under ANY chunking — pigeonhole, before you read a line
//! of code. `from_canonical_key` is the proof by example: it is a re-chunked 8-lane scheme and it
//! still loses 16 bits.
//!
//! And the aliasing is denser than the 8.74-bit deficit suggests: `2p = 4026531842 < 2^32`, so
//! **every** residue has at least two u32 preimages (`c`, `c + p`) and residues below `2^32 − 2p`
//! have three. A colliding sibling is CONSTRUCTED by adding `p` to any chunk — no grind.
//!
//! So the claim *"possession of a `Faithful8` is evidence the value came from a faithful encoder"*
//! is **false for a directly-chosen preimage**, and the type then **LAUNDERS** it: a sink cannot
//! distinguish an aliased octet from a genuinely hard one. That is the anti-launder clause
//! realized in our own code, and it is why the replacement (`dregg_codec::Digest8`) has
//! `from_bytes32`, `from_canonical_key`, and the `_DANGER` hatch **deleted, not deprecated** — a
//! wall with an escape hatch is a convention.
//!
//! Second gap, where most of the remaining wounds live: **the wall covers committed VALUES and
//! leaves map/sort KEYS bare.** Every kind-D wound is a key, and a key is a bare `BabyBear` that
//! no type ever guarded. `dregg_codec`'s `MapKey` is the type that would make those
//! unrepresentable; it is Stage 3 work.
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

/// An **8-felt commitment octet** — 8 lanes wide, not 1.
///
/// Possession of a `Faithful8` is evidence of **WIDTH ONLY**: that the value was not squeezed
/// through a single ~31-bit felt. It is **not** evidence that the 8 lanes bind their source
/// hard — `from_bytes32` and `from_canonical_key` are both `O(1)`-aliasable for a chosen
/// preimage, so for those two constructors the wall LAUNDERS the alias. See the module docs.
/// The successor with a genuinely narrow constructor set is `dregg_codec::Digest8`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Faithful8([BabyBear; 8]);

impl Faithful8 {
    /// The all-zero sentinel octet: absent carrier material (child_vk /
    /// contract_hash on a non-factory / non-hatchery block), the deployed
    /// `vk_hash == [0; 8]` revoke convention. Committed "nothing here" — not a
    /// projection of any 32-byte source.
    pub const ZERO: Self = Self([BabyBear::ZERO; 8]);

    /// The full-32-byte limb split ([`crate::effect_vm::bytes32_to_8_limbs`]): limb `i` carries
    /// bytes `[4i..4i+4]` little-endian, reduced mod `p`.
    ///
    /// ⚠ **NOT a ~124-bit binding of `b`.** This doc claimed one. The mod-`p` reduction identifies
    /// a chunk `x` with `x + p`, so a colliding pair is CONSTRUCTED in `O(1)` whenever the caller
    /// chooses the bytes. It reaches hash-strength ONLY because the intended inputs are blake3
    /// digests / VK hashes / contract hashes — i.e. the strength is the hash's, borrowed, and it
    /// evaporates the moment an attacker-chosen 32-byte value is passed here. Deleted in the
    /// successor (`dregg_codec::Digest8` has no `from_bytes32`); Stage 2/3 migration.
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

    /// The 30-bit KEY-COMMIT octet (the `pubkey8` carrier lane): 8 limbs of `8+8+8+6 = 30` bits
    /// each over the canonical 32-byte key.
    ///
    /// ⚠ **240 is the IMAGE size, not the binding.** This doc said "240 bits, faithful". The
    /// packing discards bits 6-7 of every fourth byte, so **16 source bits are unbound** and a
    /// colliding 32-byte STRING is free; only a colliding *meaningful* value costs anything
    /// (~2^120 for a pubkey that must also be a valid group element). Second-preimage is `O(1)`
    /// for a directly-chosen input. Deleted in the successor. The packing is owned by
    /// `dregg_commit::typed::canonical_32_to_felts_8` (byte-identical twin:
    /// `dregg_cell::commitment::canonical_to_babybear_pi`); this constructor
    /// takes its output and NAMES the lane so the wall stays greppable.
    #[inline]
    pub fn from_canonical_key(limbs: [BabyBear; 8]) -> Self {
        Self(limbs)
    }

    /// The v13 FIELDS-OCTET projection ([`crate::effect_vm::field_limbs8`]).
    ///
    /// ⚠ **STILL NOT FAITHFUL — but no longer `O(1)`.** This doc has now been wrong in two
    /// directions and both are recorded here on purpose.
    ///
    /// It first read "the faithful ~124-bit 8-lane split" — the same overclaim
    /// [`Faithful8::from_bytes32`]'s doc carried, and it survived that sweep. That was corrected to
    /// "`O(1)` aliasable exactly like F1", which was TRUE OF THE OLD BODY: lanes 2..7 were six
    /// `u32 % p` chunks over bytes `0..24`, and `2p < 2^32`, so a sibling with a byte-identical lane
    /// vector was CONSTRUCTED by adding `p` to any chunk, with no grind.
    ///
    /// Lanes 2..7 now carry the leading six felts of a Poseidon2 image over an INJECTIVE 16 × u16-LE
    /// preimage of the whole 32-byte value, so that constructed alias is gone: a colliding sibling
    /// must match lanes 0/1 **and** a six-felt hash. What is NOT gone is the counting argument —
    /// eight lanes carry 247.26 bits against 256, so **no 8-lane encoding of 32 bytes is injective
    /// under any chunking**, whatever the lanes contain. This constructor's octet is a
    /// hash-strength projection, not an injection, and this doc must never call it faithful.
    ///
    /// ⚑ This matters more here than at any sibling constructor: `fields[0..7]` are excluded from
    /// the byte-exact authority residue (`cell/src/commitment.rs:1099` — "bound by their own
    /// limbs"), so these lanes are their ONLY binding, and they reach
    /// `TurnReceipt::{pre,post}_state_hash`. `fields[8..15]`, which have no proof lane at all, are
    /// bound at BLAKE3 strength — the attested tier still has the weaker commitment.
    ///
    /// The layout: lane 0 = the u64-lane `lo32`, lane 1 = the u64-lane `hi32` (both unchanged
    /// deployed ABI), lanes 2..7 = the hash image (see the `field_limbs8` doc for the encoding
    /// audit). THE constructor for the `fields[0..7]` octets — it REPLACES the
    /// former eight ~31-bit `fold_bytes32_to_bb` Horner folds that rode one
    /// `from_lossy_31bit_DANGER` octet.
    ///
    /// The v13 burn-down described that earlier replacement as "closing the LAST degraded-felt
    /// residual" and it did not — it exchanged a one-felt fold for an eight-lane projection that was
    /// still `O(1)` aliasable. Width is not hardness, which is exactly what this module's header
    /// says about every other constructor. Each field's lane 0 rides its existing welded
    /// limb `4 + i`; lanes 1..7 ride the completion lanes `113 + 7·i .. +6`.
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

    /// The canonical 32-byte packing of the octet: lane `i` in bytes
    /// `[4i..4i+4]` little-endian (each BabyBear lane `< p < 2^31`, so its 4
    /// bytes recover it exactly). The exact inverse of [`Faithful8::from_bytes32`]
    /// on canonical lanes, and byte-identical to `cell::commitment::digest8_to_bytes32`.
    /// THE byte boundary: a `Faithful8` root becomes the wide 32 bytes a blake3
    /// commitment / wire slot binds — the SAME bytes the old `[u8; 32]` field
    /// held (values unchanged; only the type is now wide).
    #[inline]
    pub fn to_bytes32(&self) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, lane) in self.0.iter().enumerate() {
            out[i * 4..i * 4 + 4].copy_from_slice(&lane.as_u32().to_le_bytes());
        }
        out
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
