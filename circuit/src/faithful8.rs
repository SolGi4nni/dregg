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
//! was not: two of the named constructors are residuals, and the list below is
//! split so that reading it cannot mislead.
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
//! * [`Faithful8::from_canonical_key`] — ⚑ **the 30-bit KEY_COMMIT pubkey8 pack, and it is
//!   NOT a faithful constructor.** Reclassified 2026-08-01: its body IS
//!   `from_lossy_31bit_DANGER` (reason [`KEY_COMMIT_30BIT_RESIDUAL`]), so it now sits on the
//!   burn-down list rather than beside the tree roots. It had entered through the FRONT DOOR
//!   with a doc reading "8+8+8+6 = 30 bits per limb, 240 bits total, faithful" — and 240 bits
//!   of IMAGE is a `2^120` birthday COLLISION, against this tree's `2^123.63` floor. Below
//!   floor on the generous reading, and the true figure is `0` bits: sixteen source bits are
//!   never read, so a colliding key is one bit-flip. Full arithmetic on the constructor.
//!
//! ⚑ **THE BURN-DOWN LIST IS A GATE, NOT A CONVENTION** (2026-08-01).
//! `circuit/tests/faithful8_key_octet_below_floor.rs` walks every `*.rs` in the workspace,
//! collects the call sites of `from_lossy_31bit_DANGER` and of every ROUTER (a constructor in
//! THIS file whose body calls the hatch — `from_canonical_key` is one, derived from the source
//! rather than transcribed), and fails unless each is named in the law doc's burn-down section,
//! and unless each entry the doc carries still has a call. "Adding a `_DANGER` site without
//! listing it is a review-time violation" was a rule no instrument could enforce; a documented
//! wound is not a detected one.
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
//! * [`Faithful8::from_canonical_key`] **is** `canonical_32_to_felts_8` — family F2, 16 source
//!   bits discarded. IMAGE `2^240`; birthday COLLISION `2^120`, i.e. 3.63 bits below the
//!   `2^123.63` floor; ACTUAL collision `0`, because every fiber holds `2^16` strings and — the
//!   source being an Ed25519 public key whose x-sign is one of the discarded bits — `A` and `−A`
//!   pack identically. ⚑ It no longer admits through the front door: as of 2026-08-01 its body
//!   is the `_DANGER` hatch and it is on the burn-down list.
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

/// The `reason` string [`Faithful8::from_canonical_key`] passes to
/// [`Faithful8::from_lossy_31bit_DANGER`] — i.e. the ONE entry on the burn-down list in
/// `docs/FAITHFUL-COMMITMENT-LAW.md` as of 2026-08-01.
///
/// A residual's reason must name the residual AND its closure epoch, which is what makes the
/// grep readable without opening the law doc. The gate
/// (`circuit/tests/faithful8_key_octet_below_floor.rs`) asserts this string is quoted verbatim in
/// the doc's burn-down section, so the two cannot drift.
pub const KEY_COMMIT_30BIT_RESIDUAL: &str = "KEY_COMMIT 30-bit pubkey8 pack: image 2^240, collision 0 (16 source bits unread, Ed25519 \
     sign bit among them) — floor is 2^123.63; closes at the ninth key lane, schema epoch 16";

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
    /// ⚑ **THIS IS A NAMED RESIDUAL, NOT A FAITHFUL CONSTRUCTOR** (reclassified 2026-08-01). Its
    /// body IS [`Faithful8::from_lossy_31bit_DANGER`], carrying
    /// [`KEY_COMMIT_30BIT_RESIDUAL`] as the reason — so this octet is on the burn-down list in
    /// `docs/FAITHFUL-COMMITMENT-LAW.md` instead of standing beside the tree roots. It kept its
    /// NAME only because its two call sites
    /// (`cell::commitment::compute_rotated_pre_limbs`, `turn::rotation_witness::produce`) are the
    /// deployed producers and renaming them is a separate lane; the burn-down gate
    /// (`circuit/tests/faithful8_key_octet_below_floor.rs`) therefore greps for BOTH names.
    ///
    /// ⚠ **SAY WHICH BOUND.** Three different numbers get called "240 bits" and only one of them
    /// is a security level:
    ///
    /// * **IMAGE = `2^240`, exactly.** `lo | mid1<<8 | mid2<<16 | (hi & 0x3F)<<24` sweeps all of
    ///   `[0, 2^30)` per lane, independently, and `2^30 < p` so nothing reduces. The image is
    ///   `(2^30)^8` on the nose — `2^-7.26` of the `[0, p)^8` the octet's columns can hold.
    /// * **COLLISION (birthday, unstructured search) = `2^120`.** That is already BELOW this
    ///   tree's floor, which is `8 · log₂ p / 2 = 2^123.63` — the "~124-bit" figure the law quotes
    ///   is itself a birthday bound over a full 8-lane image, and this octet misses it by 3.63
    ///   bits. 240 bits of image is NOT at floor, which is the whole argument for the
    ///   reclassification.
    /// * **COLLISION (actual) = `0` — no search at all.** Every fiber has exactly `2^16` elements:
    ///   bits 6-7 of bytes 3, 7, 11, 15, 19, 23, 27, 31 are never read. So a second preimage on a
    ///   raw 32-byte string is one bit-flip.
    ///
    /// ⚑ And the "only a *meaningful* colliding value costs anything (~2^120)" escape this doc
    /// used to offer is **FALSE FOR THIS KEY TYPE.** The source is `Cell::public_key`, an Ed25519
    /// public key: RFC 8032 §5.1.2 puts the x-sign in **bit 7 of byte 31**, which is one of the
    /// sixteen discarded bits. So a point `A` and its negation `−A` — both valid, both
    /// decompressible, both the same order — differ in exactly that bit and pack to the
    /// **identical octet**. A colliding *valid public key* is free too. Exhibited over the real
    /// deployed packer and real curve points by
    /// `circuit/tests/faithful8_key_octet_below_floor.rs`.
    ///
    /// What closes it is a NINTH key lane — and ⚠ **say which bound for the FIX as well.** This
    /// doc read "(`2^278` image, `2^139` birthday)" until 2026-08-01. Those are the CAPACITY of
    /// nine BabyBear lanes, and `2^278.16 > 2^256` is the tell: a map out of 32 bytes has at most
    /// `2^256` images. The encoding recommended is the base-`2^29` NONET
    /// (`Dregg2.Circuit.KeyLanes9.keyToLanes9`): **image exactly `2^256`, INJECTIVE**
    /// (`keyToLanes9_injective`, from a total decoder and a machine-checked left inverse), so the
    /// encoding step loses **nothing**, there is no encoding collision to bound, and the binding
    /// reduces to the sponge that absorbs the lanes. ⚠ Rung: proved in Lean, **not emitted and not
    /// consumed by a verifier**.
    ///
    /// The geometry is `rotatedNumPreLimbs` 184 → 187, `B_SPAN` 247 → 251, a descriptor re-emit and
    /// a VK rotation. ⚑ **Re-checked 2026-08-01 and the two numbers hold; the epoch did not.**
    /// `184 → 187` is right and `185` is not: `B_SPAN := n + 3 + (n − 4) / 3` is `Nat` floor
    /// division while the carrier chain steps every three limbs, so the unwritten invariant is
    /// `rotatedNumPreLimbs ≡ 1 (mod 3)` — `184 % 3 = 187 % 3 = 1`, `185 % 3 = 2` — and `187` buys
    /// exactly the three ninth lanes the counting demands (`public_key`, `child_vk`,
    /// `contract_hash`, all three 8-lane). `187 + 3 + 61 = 251` confirms `B_SPAN`. The epoch figure
    /// read "15 → 16" and was stale by four: `CANONICAL_STATE_SCHEMA_EPOCH` is at **19**, so the
    /// geometry move is 19 → 20. Not this lane's edit — this lane's edit is that the wall stops
    /// calling it faithful while that is pending, and that the price is stated against the constant
    /// rather than against a remembered one. The packing itself is owned by
    /// `dregg_commit::typed::canonical_32_to_felts_8` (byte-identical twin:
    /// `dregg_cell::commitment::canonical_to_babybear_pi`) and is UNCHANGED here.
    #[inline]
    pub fn from_canonical_key(limbs: [BabyBear; 8]) -> Self {
        Self::from_lossy_31bit_DANGER(KEY_COMMIT_30BIT_RESIDUAL, limbs)
    }

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
    /// riding in one octet, or — the current entry — a pack that never reads
    /// sixteen of its source bits). `reason` must name the residual and its
    /// closure epoch.
    ///
    /// ⚑ **Current list: ONE residual**, the KEY_COMMIT 30-bit pubkey8 pack
    /// ([`KEY_COMMIT_30BIT_RESIDUAL`]), reached through
    /// [`Faithful8::from_canonical_key`] from `cell::commitment::compute_rotated_pre_limbs` and
    /// `turn::rotation_witness::produce`. The list was recorded as "EMPTY (v13 DONE)" until
    /// 2026-08-01; it was empty only because the key octet had been let in the front door.
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
