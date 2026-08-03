//! # `Faithful8` — the faithful-commitment TYPE WALL.
//!
//! `docs/FAITHFUL-COMMITMENT-LAW.md`: every 32-byte component that flows into
//! the deployed state commitment binds its SOURCE at the system's own soundness
//! strength — never a lossy 1-felt projection.
//!
//! ⚠ **SAY WHICH BOUND.** The law's floor reads "~124-bit"; it is `8 · log₂ p / 2 = 2^123.63`, a
//! **birthday COLLISION** bound over a full 8-lane IMAGE of `2^247.26`. Image size and collision
//! cost are the pair this tree keeps confusing, and quoting the flattering one is how a `2^15.5`
//! object once claimed 124 bits — and how the `2^120` key octet below sat in the faithful list.
//!
//! The insidious failure mode the law names: **a bare `BabyBear` limb carries no
//! evidence of faithful-vs-degraded.** A faithful 8-felt binding and a degraded
//! ~31-bit Horner fold are the same type (`[BabyBear; 8]` / `BabyBear`), so a
//! lossy fold once slid into the commitment silently and was found only by a
//! bit-audit months later. The ast-grep gate (`scripts/check-no-degraded-felt.sh`)
//! catches the *pattern* in the three known producers; THIS newtype is the
//! *type-level* wall: a commitment-bearing octet sink takes `Faithful8`, and a
//! `Faithful8` can only be built through a NAMED constructor — so a degraded
//! felt in a commitment position is a **compile error**, everywhere, including
//! files the gate has never heard of. ⚑ "Named" is the honest word and "faithful"
//! is not: the two KEY residuals that made that sentence necessary are DELETED as of
//! 2026-08-02, but `from_bytes32` still admits an `O(1)`-aliasable octet through the front
//! door, so the list below stays split and the honest section stays where it is.
//!
//! ## The constructor discipline
//!
//! The inner `[BabyBear; 8]` is **private**. The only ways in:
//!
//! * [`Faithful8::from_bytes32`] — the canonical full-32-byte limb split
//!   ([`crate::effect_vm::bytes32_to_8_limbs`]): 8 × 4-byte little-endian limbs.
//!   ⚠ Full `2^247.26` IMAGE but collision cost **`0`** for an attacker-chosen
//!   input (`v` and `v + p` alias, `2p < 2^32`); at strength only where the input
//!   is a hash output, which makes safety a **per-site obligation** rather than a
//!   property of the constructor. Its commitment-bearing sites take `child_vk` /
//!   `contract_hash`, and many others are lane REPACKING (canonical felts → bytes →
//!   back), where it is an exact inverse. ⚠ Not audited exhaustively, and
//!   `cell/src/state.rs`'s serde `deserialize` does NOT fit the pattern — it reduces
//!   32 bytes taken off the wire. This bullet used to say "~124-bit binding of the
//!   source bytes" while the constructor's own doc, forty lines down, said "NOT a
//!   ~124-bit binding of `b`". Both readings were in the same file.
//! * the **tree roots** — the cap/heap/fields sorted-Poseidon2 `node8` trees
//!   return `Faithful8` directly from their root fold
//!   ([`crate::cap_root::compute_capability_root_with_tombstones`],
//!   [`crate::heap_root::compute_canonical_heap_root_8`],
//!   [`crate::heap_root::CanonicalHeapTree8::root8`], …); internally they use
//!   the crate-private [`Faithful8::from_root8`].
//! * the **wire-commit chain** — [`Faithful8::from_wire_commit`] /
//!   [`Faithful8::from_wire_commit_chip`], the chained 8-felt rotated state
//!   commitment (`poseidon2::wire_commit_8` / `wire_commit_8_chip`).
//! * [`Faithful8::ZERO`] — the all-zero sentinel (absent carrier material, the
//!   deployed `vk_hash == [0; 8]` revoke convention). Zero is not a projection
//!   of anything; it is the committed "nothing here" value.
//! * [`Faithful8::from_lossy_31bit_DANGER`] — the **greppable escape hatch** for
//!   the named, allowlisted residuals. Every call site is a burn-down list entry, and
//!   adding one without updating `docs/FAITHFUL-COMMITMENT-LAW.md` is a review-time
//!   violation — ⚑ now a *test-time* one as well, see the gate below.
//!
//! ⚑ **THE OWNER-KEY OCTET IS GONE — the burn-down list is EMPTY as of 2026-08-02.** The key's
//! two entries in this list (`from_canonical_key`, then its successor `from_key_nonet_low8`) are
//! both **deleted**, not deprecated, together with the reason constant they carried. The last of
//! them projected the injective base-`2^29` nonet down to its low eight lanes because
//! `B_PUBKEY_OCTET` is eight columns wide and lane 8 had no home; the 187-limb geometry gives
//! lane 8 in-block limb 186, so the projection has no reason to exist and there is no
//! `Faithful8` path to an owner-key octet at all. The successor is [`crate::Faithful9`]'s
//! `from_key_lanes9` over `effect_vm::PUBKEY_NONET_LANE_COL`.
//!
//! ⚠ **An empty burn-down list is not the same claim as "everything here is faithful".** It says
//! only that nothing currently routes through the hatch. `from_bytes32` still admits through the
//! front door and is still `O(1)`-aliasable — see the section below, which is the honest one.
//!
//! ⚑ **THE BURN-DOWN LIST IS A GATE, NOT A CONVENTION** (2026-08-01).
//! `circuit/tests/faithful8_key_octet_below_floor.rs` walks every `*.rs` in the workspace,
//! collects the call sites of `from_lossy_31bit_DANGER` and of every ROUTER (a constructor in
//! THIS file whose body calls the hatch — derived from the source rather than transcribed),
//! and fails unless each is named in the law doc's burn-down section,
//! and unless each entry the doc carries still has a call. "Adding a `_DANGER` site without
//! listing it is a review-time violation" was a rule no instrument could enforce; a documented
//! wound is not a detected one. The match is BIDIRECTIONAL, which is why deleting the
//! constructor and deleting its doc rows had to land in one commit.
//!
//! ⚑ **The key is the `(file, reason-constant)` pair, not the file path** — corrected the same day
//! the gate was written. Keyed on paths, it caught a NEW file and was blind inside the three files
//! it already listed, which are the two deployed producers and this one: precisely where the next
//! degraded octet gets added. Consequences for a residual added here: its reason must be a `&str`
//! constant declared in this file (an inline literal at the call site is refused), and the law
//! doc's burn-down section must quote that constant's VALUE verbatim.
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
//! * `Faithful8::from_canonical_key` **was** `canonical_32_to_felts_8` — family F2, 16 source
//!   bits discarded. IMAGE `2^240`; birthday COLLISION `2^120`, i.e. 3.63 bits below the
//!   `2^123.63` floor; ACTUAL collision `0`, because every fiber holds `2^16` strings and — the
//!   source being an Ed25519 public key whose x-sign is one of the discarded bits — `A` and `−A`
//!   pack identically. ⚑ **GONE.** It was reclassified onto the burn-down list on 2026-08-01, its
//!   successor `from_key_nonet_low8` (the injective nonet's low eight lanes, 232 bits, the SAME
//!   `A`/`−A` merge) inherited the entry, and both are **deleted 2026-08-02** — the flag day that
//!   gave lane 8 a column. Successor: [`crate::Faithful9::from_key_lanes9`], image exactly
//!   `2^256`, injective, with a total decoder that reads the 32 bytes back.
//! * `Faithful8::from_field_limbs8` **was** `field_limbs8` — family F3, the constructor that fed
//!   `fields[0..7]`, the only octet in the v9 commitment with no byte-exact companion and therefore
//!   the one where an alias reached the signed anchor. ⚑ **GONE — deleted 2026-07-31, together with
//!   `field_limbs8` and its `field_value_preimage`.** Its successor is [`crate::Faithful9`] over the
//!   nine-lane [`crate::effect_vm::field_limbs9`], whose injectivity is a Lean theorem with a total
//!   decoder and a machine-checked left inverse. F3 was `O(1)`-aliasable, then hash-contained at a
//!   **2^92.7 collision** — below this tree's ~124-bit bar — and never injective, because it could
//!   not be: the counting argument below applies to every 8-lane scheme regardless of what the lanes
//!   carry. The right fix was a ninth lane; the containment was not a step toward it.
//!
//! ⚑ **THE COUNTING ARGUMENT, which subsumes every entry above.** `p = 2013265921`, so
//! `log2 p = 30.907` and eight lanes carry **247.26 bits** against a 32-byte field's **256**. No
//! 8-lane encoding of 32 bytes is injective under ANY chunking — pigeonhole, before you read a line
//! of code. The retired `from_canonical_key` is the proof by example: it was a re-chunked 8-lane
//! scheme and it still lost 16 bits.
//!
//! And the aliasing is denser than the 8.74-bit deficit suggests: `2p = 4026531842 < 2^32`, so
//! **every** residue has at least two u32 preimages (`c`, `c + p`) and residues below `2^32 − 2p`
//! have three. A colliding sibling is CONSTRUCTED by adding `p` to any chunk — no grind.
//!
//! So the claim *"possession of a `Faithful8` is evidence the value came from a faithful encoder"*
//! is **false for a directly-chosen preimage**, and the type then **LAUNDERS** it: a sink cannot
//! distinguish an aliased octet from a genuinely hard one. That is the anti-launder clause
//! realized in our own code, and it is why the replacement (`dregg_codec::Digest8`) has
//! `from_bytes32`, the key packs, and the `_DANGER` hatch **deleted, not deprecated** — a
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

// ⚑ `KEY_NONET_NINTH_LANE_UNBOUND` — the reason string the owner-key octet rode into
// `from_lossy_31bit_DANGER` — is DELETED (2026-08-02), together with `from_key_nonet_low8` and
// the three rows it owned in `docs/FAITHFUL-COMMITMENT-LAW.md`'s burn-down list. It said
// "`state_commit` absorbs lanes 0..=7 only — 232 of 256 key bits, Ed25519 sign bit NOT among
// them", and that sentence is now false: the 187-limb geometry gives lane 8 in-block limb 186,
// both producers write the full nonet through `Faithful9::from_key_lanes9`, and `wireCommitR`
// folds `[0, 187)`.
//
// It is deleted rather than kept as an empty allowlist entry because a residual retained after
// its residue is gone is worse than one that means something: the next reader trusts it. The
// burn-down list is a bidirectional set match — an entry with no call site reds exactly as loudly
// as a call site with no entry — so the constant, the constructor and the doc rows had to go in
// ONE commit, and did.

/// An **8-felt commitment octet** — 8 lanes wide, not 1.
///
/// Possession of a `Faithful8` is evidence of **WIDTH ONLY**: that the value was not squeezed
/// through a single ~31-bit felt. It is **not** evidence that the 8 lanes bind their source
/// hard — `from_bytes32` is `O(1)`-aliasable for a chosen preimage, so for that constructor the
/// wall LAUNDERS the alias. See the module docs.
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

    // ⚑ `from_key_nonet_low8` — the owner-key projection — is DELETED (2026-08-02). It took the
    // injective base-`2^29` nonet and threw lane 8 away, because `B_PUBKEY_OCTET` is eight columns
    // wide and lane 8 had no home in the 184-limb geometry. That made the signed consensus anchor
    // a 232-of-256-bit binding of the owner key, and the 24 bits it dropped contain the Ed25519
    // x-sign (RFC 8032 §5.1.2, bit 7 of byte 31) — so `A` and `−A` committed identically, at cost
    // zero and with no search.
    //
    // Its replacement is not another `Faithful8` constructor. It is [`crate::Faithful9`]'s
    // `from_key_lanes9` over `effect_vm::PUBKEY_NONET_LANE_COL` (lanes 0..=7 at 105..=112, lane 8
    // at 186), so there is no `Faithful8` path to an owner-key octet any more and a caller that
    // wants one gets a compile error — which is the point of the wall.
    //
    // ⚠ Do NOT "restore" this as a low-eight helper for some other sink. The retired 30-bit octet
    // carried 240 bits and this projection carried 232, and BOTH dropped bit 7 of byte 31: neither
    // was a repair, and no eight-lane encoding of 32 bytes can be one (`p^8 < 2^256`).

    // ⚑ `from_field_limbs8` — the v13 FIELDS-OCTET constructor — is DELETED (2026-07-31), and so is
    // the `field_limbs8` encoder behind it. It fed `fields[0..7]`, which are excluded from the
    // byte-exact authority residue ("bound by their own limbs"), so its octet was their ONLY binding
    // and it reached `TurnReceipt::{pre,post}_state_hash`, the executor signature and the receipt QC.
    //
    // Its doc was wrong in two directions before it died, which is the reason this note exists rather
    // than a silent removal. It first read "the faithful ~124-bit 8-lane split"; corrected to "`O(1)`
    // aliasable exactly like F1" (true of the `u32 % p` body); then the lanes became a Poseidon2
    // image over an injective preimage and the honest number was a **2^92.7 COLLISION** — quoted at
    // the time as "~2^185", which is the SECOND-PREIMAGE figure for the same object. Below this
    // tree's ~124-bit bar either way.
    //
    // The successor is [`crate::Faithful9`] over [`crate::effect_vm::field_limbs9`]: nine lanes,
    // injective as a Lean theorem (`fieldToLanes9_injective`, from a total decoder and a
    // machine-checked left inverse), lanes 0/1 byte-identically the deployed kernel u64 lane. There
    // is no `Faithful8` path to a fields octet any more — a caller that wants one gets a compile
    // error, which is the point of the wall.

    /// **THE GREPPABLE ESCAPE HATCH** for the NAMED degraded residuals
    /// (`docs/FAITHFUL-COMMITMENT-LAW.md` — the burn-down list). A call
    /// site of this constructor is an admission: these 8 limbs do NOT each
    /// bind a faithful source (e.g. eight independent ~31-bit Horner folds
    /// riding in one octet, or a pack that never reads sixteen of its source
    /// bits). `reason` must name the residual and WHAT CLOSES IT — never a
    /// remembered schema-epoch NUMBER, which is a pin against nothing.
    ///
    /// ⚑ **Current list: EMPTY, as of 2026-08-02** — the owner-key octet was the last entry and
    /// its ninth lane now reaches the anchor, so `from_key_nonet_low8`, its reason constant and
    /// its three doc rows are all deleted.
    ///
    /// ⚠ **This has read "EMPTY" before and been wrong.** It said "EMPTY (v13 DONE)" through
    /// 2026-08-01 while the key octet sat in the tree — empty only because that octet had been let
    /// in the FRONT DOOR as a named constructor rather than through this hatch. So an empty list is
    /// evidence about the hatch and about nothing else; the wall's real limits are in the module
    /// docs' "WHAT THIS WALL DOES NOT GUARD" section, and `from_bytes32` is still in them.
    ///
    /// Call sites are no longer merely "reviewed against the law doc's allowlist" — that was a
    /// convention with no instrument. `circuit/tests/faithful8_key_octet_below_floor.rs` now
    /// fails the suite on a site the doc does not name, and on a doc entry with no site.
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
