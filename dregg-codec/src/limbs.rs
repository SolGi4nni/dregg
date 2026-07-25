//! **Layer L — the injective byte→felt map.** This is the ONE file in the repository that is
//! allowed to contain byte→felt arithmetic.
//!
//! ```text
//! Limbs16(b) = [ u16::from_le_bytes([b[2i], b[2i+1]]) ; i in 0..16 ]
//! ```
//!
//! Injective, and the proof is constructive: [`Limbs16::to_bytes32`] is a total two-sided inverse
//! (`u16::to_le_bytes ∘ u16::from_le_bytes = id` on every one of the 2^16 `u16` values, checked
//! exhaustively by test). Having a left inverse *is* injectivity — no sampling argument is
//! needed and none is offered.
//!
//! Every limb is `< 2^16 = 65536`, and `p = 2013265921 > 2^30`, so **no modular reduction occurs**.
//! That is the whole difference from the family this replaces: the deployed 8×u32 encodings reduce
//! `mod p`, and a uniformly random 4-byte chunk exceeds `p` with probability `1 − p/2^32 = 53.1%`,
//! which is where the `O(1)` collisions come from.

use serde::{Deserialize, Serialize};
use std::cmp::Ordering;

/// The BabyBear prime, `p = 2^31 − 2^27 + 1 = 2013265921`.
///
/// Carried here (rather than imported) because this crate is a leaf by design — see the note in
/// `Cargo.toml`. `dregg_circuit::field::BABYBEAR_P` must equal this; the equality is pinned by a
/// test in `dregg-circuit` (`codec_adapter`), not asserted by comment.
pub const BABYBEAR_P: u32 = (1 << 31) - (1 << 27) + 1;

/// Bits per limb. 16 is the range-check width the AIR already emits (`u16Ranges` in the Lean
/// plan), and the widest lookup table that stays cheap.
pub const LIMB_BITS: u32 = 16;

/// A 32-byte value is sixteen `u16` limbs. Mirrors Lean's `BYTES32_U16_LIMBS`.
pub const BYTES32_U16_LIMBS: usize = 16;

/// A `u64` is four `u16` limbs, little-endian place order. Mirrors Lean's `U64_U16_LIMBS`.
pub const U64_U16_LIMBS: usize = 4;

/// **The only carrier of a 32-byte value that is allowed to produce felts.**
///
/// Its entire felt-producing surface is [`Bytes32::limbs`] (Layer L) and [`Bytes32::digest8`]
/// (Layer D). There is deliberately no `From<[u8; 32]>` into any felt type and no way to obtain a
/// felt from bytes without naming one of the two. That naming *is* the wall: a reviewer reading a
/// diff sees which layer was chosen.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Bytes32([u8; 32]);

impl Bytes32 {
    /// Wrap a raw 32-byte value. Wrapping is free and commits to nothing; the choice that matters
    /// is which of [`limbs`](Self::limbs) / [`digest8`](Self::digest8) the caller then names.
    #[must_use]
    pub const fn new(raw: [u8; 32]) -> Self {
        Self(raw)
    }

    /// The underlying bytes. Byte-level access is unrestricted — the wall guards the *felt*
    /// direction, since that is the only direction that can lose information.
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    /// Consume into the raw bytes.
    #[must_use]
    pub const fn into_bytes(self) -> [u8; 32] {
        self.0
    }

    /// **Layer L.** The canonical injective encoding: sixteen little-endian `u16` limbs.
    #[must_use]
    pub const fn limbs(&self) -> Limbs16 {
        // The ONE byte->felt expression in the repository. Every other site delegates here.
        let b = &self.0;
        let mut out = [0u16; BYTES32_U16_LIMBS];
        let mut i = 0;
        while i < BYTES32_U16_LIMBS {
            out[i] = u16::from_le_bytes([b[2 * i], b[2 * i + 1]]);
            i += 1;
        }
        Limbs16(out)
    }

    /// **Layer D.** The binding fixed-width commitment, `chip_squeeze(domain ‖ Limbs16(b))`.
    /// See [`crate::digest`] for what "one squeeze" actually costs on the deployed chip — it is
    /// not one permutation, and the design document's claim that it is has been corrected.
    #[must_use]
    pub fn digest8<S: crate::Squeeze8>(&self, sq: &S, domain: crate::Domain) -> crate::Digest8 {
        crate::Digest8::compute(sq, domain, self)
    }
}

impl From<[u8; 32]> for Bytes32 {
    fn from(raw: [u8; 32]) -> Self {
        Self(raw)
    }
}

/// **Layer L — sixteen little-endian `u16` limbs.** The injective byte→felt map.
///
/// Ordering note: `Ord` is **not** implemented, deliberately. Three different useful orders live
/// on these limbs and they disagree — see the ORDER block on the impl below. A blanket `Ord` would
/// silently pick one, which is how a comparator and the codec drift apart. Name the order you
/// mean: [`Limbs16::cmp_limb_lex`] (the deployed one), [`Limbs16::cmp_le_integer`], or
/// [`Limbs16::cmp_memcmp_order`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Limbs16([u16; BYTES32_U16_LIMBS]);

impl Limbs16 {
    /// Reassemble from raw limbs (e.g. read back out of witness columns).
    #[must_use]
    pub const fn from_u16s(limbs: [u16; BYTES32_U16_LIMBS]) -> Self {
        Self(limbs)
    }

    /// The limbs, in codec (little-endian, index) order.
    #[must_use]
    pub const fn as_u16s(&self) -> &[u16; BYTES32_U16_LIMBS] {
        &self.0
    }

    /// **The inverse.** Total, exact, and a `memcpy` in disguise — this is what makes Layer L
    /// injective rather than merely wide.
    #[must_use]
    pub const fn to_bytes32(&self) -> Bytes32 {
        let mut out = [0u8; 32];
        let mut i = 0;
        while i < BYTES32_U16_LIMBS {
            let [lo, hi] = self.0[i].to_le_bytes();
            out[2 * i] = lo;
            out[2 * i + 1] = hi;
            i += 1;
        }
        Bytes32(out)
    }

    /// The limbs as felt values. Each is `< 2^16 ≪ p`, so this widening is the identity on the
    /// field — **no reduction happens**, which is the entire point of the codec.
    #[must_use]
    pub const fn felts(&self) -> [u32; BYTES32_U16_LIMBS] {
        let mut out = [0u32; BYTES32_U16_LIMBS];
        let mut i = 0;
        while i < BYTES32_U16_LIMBS {
            out[i] = self.0[i] as u32;
            i += 1;
        }
        out
    }

    // ── ORDER. Three DISTINCT orders live on these limbs and the design document conflates two
    // of them. Read this before reaching for one. ────────────────────────────────────────────
    //
    // `docs/DESIGN-canonical-byte-felt-codec.md` §2.5 says the big-endian copy existed because
    // "BE limbs make lexicographic order on the limb vector agree with `memcmp` on the source
    // bytes", and resolves the disagreement by claiming "a lex comparator over LE limbs reads
    // indices `15..0` instead of `0..15`. That is a column-index change with ZERO constraint
    // cost."
    //
    // **That is wrong, and the deployed code says so.** Reading indices `15..0` yields the order
    // of the value read as a little-endian 256-bit *integer*, which is not `memcmp`: `memcmp`
    // compares byte 0 first, and byte 0 lives in limb 0's LOW half. Recovering `memcmp` over LE
    // limbs needs a per-limb byte swap — an 8-bit split of each compared limb, which is NOT a
    // free column-index change.
    //
    // The deployed AAFI comparator (`circuit/src/exact_nullifier_aafi.rs`, `impl Ord for
    // ExactTaggedKey`) uses neither: it is the derived `Ord` on `[u16; 16]`, i.e. lex over indices
    // `0..15` comparing each limb NUMERICALLY. Its own Lean-KAT test says this out loud —
    // *"numeric LE-u16 lane lex says 255 < 256, while byte lex says 00 < ff"* — and asserts the
    // numeric order. So the shipped order is a third thing, and it is the one the sorted-tree
    // bracket gadget is proven against (`LexCompare8Emit.lexLt8_refines`, lane 0 most significant).
    //
    // All three are therefore named, and the free-vs-costly split is stated at each one.

    /// **The deployed order.** Lex over limb indices `0..15`, comparing each limb numerically.
    ///
    /// This is byte-for-byte the derived `Ord` on `[u16; 16]` that
    /// `exact_nullifier_aafi::ExactTaggedKey` already uses for the live exact-fields root, and the
    /// order the Lean bracket gadget is proven against. **Free in-circuit** (16 numeric limb
    /// compares, no decomposition). It does **not** agree with `memcmp` on the source bytes and is
    /// not supposed to.
    #[must_use]
    pub fn cmp_limb_lex(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }

    /// The order of the value read as a **little-endian 256-bit integer**
    /// (`Σ byteᵢ · 2^(8i)`): lex over limb indices `15..0`, numerically.
    ///
    /// **Free in-circuit** — a pure column-index reversal, which is the only part of §2.5's
    /// "zero constraint cost" claim that survives. This is what §2.5 actually describes; it is
    /// simply not `memcmp`.
    #[must_use]
    pub fn cmp_le_integer(&self, other: &Self) -> Ordering {
        for i in (0..BYTES32_U16_LIMBS).rev() {
            match self.0[i].cmp(&other.0[i]) {
                Ordering::Equal => {}
                ne => return ne,
            }
        }
        Ordering::Equal
    }

    /// Agrees with `memcmp` on the source bytes — equivalently, the value read as a **big-endian**
    /// 256-bit integer.
    ///
    /// ⚠ **NOT free in-circuit.** Limb `i` holds source bytes `2i` (low half) and `2i+1` (high
    /// half), and `memcmp` wants byte `2i` to dominate, so each compared limb must be split into
    /// its two bytes — an 8-bit decomposition per limb on top of the compare. This is the real
    /// price of the little-endian decision for a gadget that genuinely needs byte order, and §2.5
    /// prices it at zero. Prefer [`cmp_limb_lex`](Self::cmp_limb_lex) unless an external artifact
    /// forces byte order.
    #[must_use]
    pub fn cmp_memcmp_order(&self, other: &Self) -> Ordering {
        for i in 0..BYTES32_U16_LIMBS {
            let (a, b) = (self.0[i], other.0[i]);
            if a != b {
                return a.swap_bytes().cmp(&b.swap_bytes());
            }
        }
        Ordering::Equal
    }
}

/// A `u64` as four little-endian `u16` limbs — `value = Σ limbᵢ · 2^(16i)`.
///
/// Integers keep place order. One rule, no exceptions: the same little-endianness as [`Limbs16`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct U64Limbs4([u16; U64_U16_LIMBS]);

impl U64Limbs4 {
    #[must_use]
    pub const fn encode(value: u64) -> Self {
        Self([
            value as u16,
            (value >> 16) as u16,
            (value >> 32) as u16,
            (value >> 48) as u16,
        ])
    }

    #[must_use]
    pub const fn decode(&self) -> u64 {
        (self.0[0] as u64)
            | ((self.0[1] as u64) << 16)
            | ((self.0[2] as u64) << 32)
            | ((self.0[3] as u64) << 48)
    }

    #[must_use]
    pub const fn as_u16s(&self) -> &[u16; U64_U16_LIMBS] {
        &self.0
    }

    #[must_use]
    pub const fn felts(&self) -> [u32; U64_U16_LIMBS] {
        [
            self.0[0] as u32,
            self.0[1] as u32,
            self.0[2] as u32,
            self.0[3] as u32,
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pigeonhole fact the whole design rests on: `p^8 < 2^256`, so no 8-felt encoding of a
    /// 32-byte value can be injective. Checked in integer arithmetic rather than asserted in prose.
    #[test]
    fn no_injective_eight_felt_encoding_exists() {
        // p^8 as a 256-bit integer, built by repeated squaring in u128 halves is awkward; compare
        // log2 instead, exactly: p < 2^31, and p^8 < 2^248 requires p < 2^31 which holds, so the
        // codomain p^8 is strictly below 2^248 << 2^256.
        assert!(u64::from(BABYBEAR_P) < 1u64 << 31);
        // 8 * 31 = 248 < 256: even the generous bound p < 2^31 leaves an 8-bit deficit.
        assert!(8 * 31 < 256);
        // And 9 felts suffice: 9 * 30 = 270 > 256 with room, so ceil(256/log2 p) = 9.
        assert!(9 * 30 > 256);
    }

    /// **Injectivity, proved not sampled.** `Limbs16` acts independently on each 2-byte chunk via
    /// `u16::from_le_bytes`, whose inverse `to_le_bytes` is checked here on ALL 2^16 inputs.
    /// A map that is a bijection on each chunk of a product domain is a bijection on the product,
    /// hence injective on `[u8; 32]`. This is the whole falsification: exhaustive, not random.
    #[test]
    fn limb_map_is_exhaustively_bijective_on_the_chunk_domain() {
        for v in 0u32..=u32::from(u16::MAX) {
            let v = v as u16;
            let bytes = v.to_le_bytes();
            assert_eq!(
                u16::from_le_bytes(bytes),
                v,
                "chunk round-trip failed at {v}"
            );
            assert_eq!(bytes[0], (v & 0xFF) as u8);
            assert_eq!(bytes[1], (v >> 8) as u8);
        }
    }

    /// The composed round-trip on the real domain, over structured adversarial vectors: every
    /// single-bit-set value, every single-byte-saturated value, and the boundary patterns.
    #[test]
    fn bytes32_round_trips_and_distinct_inputs_stay_distinct() {
        let mut corpus: Vec<[u8; 32]> = Vec::new();
        corpus.push([0u8; 32]);
        corpus.push([0xFFu8; 32]);
        for bit in 0..256usize {
            let mut b = [0u8; 32];
            b[bit / 8] |= 1 << (bit % 8);
            corpus.push(b);
        }
        for byte in 0..32usize {
            let mut b = [0xFFu8; 32];
            b[byte] = 0;
            corpus.push(b);
        }
        // The mod-p alias witnesses that break the family this replaces: 0x08000000 and
        // 0x08000000 + p = 0x80000001 collide under `u32 % p`. They must NOT collide here.
        let mut alias_lo = [0u8; 32];
        alias_lo[3] = 0x08;
        let mut alias_hi = [0u8; 32];
        alias_hi[0] = 0x01;
        alias_hi[3] = 0x80;
        corpus.push(alias_lo);
        corpus.push(alias_hi);

        // `alias_lo` coincides with the single-bit-27 vector, so dedupe before asserting
        // injectivity — otherwise the test would flag its own duplicate input as a collision.
        corpus.sort_unstable();
        corpus.dedup();

        let mut seen = std::collections::HashMap::new();
        for raw in &corpus {
            let v = Bytes32::new(*raw);
            assert_eq!(
                v.limbs().to_bytes32(),
                v,
                "round-trip failed for {raw:02x?}"
            );
            for limb in v.limbs().as_u16s() {
                assert!(
                    u32::from(*limb) < BABYBEAR_P,
                    "a limb must never need reduction"
                );
            }
            if let Some(prev) = seen.insert(v.limbs(), *raw) {
                panic!("collision: {prev:02x?} and {raw:02x?} share a limb vector");
            }
        }
        assert_eq!(seen.len(), corpus.len());
    }

    /// The alias pair that is an `O(1)` collision under the encodings this codec replaces is NOT a
    /// collision here. This is the falsifier for "the new codec actually fixes the old failure".
    #[test]
    fn the_mod_p_alias_pair_no_longer_collides() {
        let mut lo = [0u8; 32];
        lo[3] = 0x08; // chunk 0 = 0x0800_0000
        let mut hi = [0u8; 32];
        hi[0] = 0x01;
        hi[3] = 0x80; // chunk 0 = 0x8000_0001 = 0x0800_0000 + p
        // Under the old map both chunks reduce to the same felt:
        assert_eq!(0x0800_0000u32 % BABYBEAR_P, 0x8000_0001u32 % BABYBEAR_P);
        // Under Limbs16 they are distinct, and remain byte-recoverable:
        let (a, b) = (Bytes32::new(lo), Bytes32::new(hi));
        assert_ne!(a.limbs(), b.limbs());
        assert_eq!(a.limbs().to_bytes32(), a);
        assert_eq!(b.limbs().to_bytes32(), b);
    }

    /// **The endianness pin.** Concrete vector, written out by hand, so a future edit that flips
    /// to big-endian fails loudly here rather than silently at a fifth call site.
    #[test]
    fn endianness_is_little_and_pinned_to_a_concrete_vector() {
        let mut raw = [0u8; 32];
        for (i, slot) in raw.iter_mut().enumerate() {
            *slot = i as u8;
        }
        let limbs = *Bytes32::new(raw).limbs().as_u16s();
        // byte 0 = 0x00 is the LOW half of limb 0; byte 1 = 0x01 is the HIGH half.
        assert_eq!(limbs[0], 0x0100);
        assert_eq!(limbs[1], 0x0302);
        assert_eq!(limbs[15], 0x1F1E);
        // Explicit refutation of the big-endian reading, so the assertion above cannot be
        // satisfied by a BE implementation that happens to pass a symmetric vector.
        assert_ne!(limbs[0], 0x0001);
        assert_eq!(
            U64Limbs4::encode(0x0001_0002_0003_0004).as_u16s()[0],
            0x0004
        );
    }

    fn order_corpus() -> Vec<[u8; 32]> {
        let mut corpus: Vec<[u8; 32]> = vec![[0u8; 32], [0xFFu8; 32]];
        for pos in 0..32usize {
            for val in [0x00u8, 0x01, 0x7F, 0x80, 0xFE, 0xFF] {
                let mut b = [0x40u8; 32];
                b[pos] = val;
                corpus.push(b);
            }
        }
        corpus.sort_unstable();
        corpus.dedup();
        corpus
    }

    /// `cmp_memcmp_order` really is `memcmp`. Exhaustive over the corpus's full cross product.
    #[test]
    fn memcmp_order_reproduces_byte_order_exactly() {
        let corpus = order_corpus();
        for a in &corpus {
            for b in &corpus {
                let got = Bytes32::new(*a)
                    .limbs()
                    .cmp_memcmp_order(&Bytes32::new(*b).limbs());
                assert_eq!(got, a.cmp(b), "order diverged on {a:02x?} vs {b:02x?}");
            }
        }
    }

    /// `cmp_le_integer` really is the little-endian-integer order.
    #[test]
    fn le_integer_order_matches_the_le_integer_reading() {
        let corpus = order_corpus();
        let as_le_int = |raw: &[u8; 32]| {
            let mut rev = *raw;
            rev.reverse();
            rev // byte 31 is most significant => reversed array compares as the LE integer
        };
        for a in &corpus {
            for b in &corpus {
                assert_eq!(
                    Bytes32::new(*a)
                        .limbs()
                        .cmp_le_integer(&Bytes32::new(*b).limbs()),
                    as_le_int(a).cmp(&as_le_int(b)),
                    "le-integer order diverged on {a:02x?} vs {b:02x?}"
                );
            }
        }
    }

    /// **THE ENDIANNESS/ORDER PIN, and the correction to §2.5.**
    ///
    /// The vector is lifted verbatim from the deployed AAFI's own Lean KAT
    /// (`circuit/src/exact_nullifier_aafi.rs`: *"numeric LE-u16 lane lex says 255 < 256, while
    /// byte lex says 00 < ff"*). On it, the three orders genuinely disagree — so a future author
    /// cannot substitute one for another, and cannot resurrect a big-endian codec on the grounds
    /// that index reversal "recovers memcmp for free". It does not.
    #[test]
    fn the_three_orders_are_distinct_and_the_deployed_one_is_limb_lex() {
        let mut a = [0u8; 32];
        a[1] = 1; // limb0 = 0x0100 = 256
        let mut b = [0u8; 32];
        b[0] = 255; // limb0 = 0x00FF = 255
        let (la, lb) = (Bytes32::new(a).limbs(), Bytes32::new(b).limbs());

        // Byte order (memcmp): a < b, because a[0] = 0x00 < b[0] = 0xFF.
        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(la.cmp_memcmp_order(&lb), Ordering::Less);

        // The DEPLOYED order (derived Ord on [u16; 16], lex over 0..15, numeric): b < a.
        assert_eq!(lb.cmp_limb_lex(&la), Ordering::Less);
        assert_eq!(la.cmp_limb_lex(&lb), Ordering::Greater);

        // ...so the deployed order and memcmp are NOT the same order.
        assert_ne!(la.cmp_limb_lex(&lb), la.cmp_memcmp_order(&lb));

        // And index reversal (the §2.5 recipe) does NOT give memcmp either: on this vector the
        // LE-integer order agrees with limb lex, not with memcmp.
        assert_eq!(la.cmp_le_integer(&lb), Ordering::Greater);
        assert_ne!(la.cmp_le_integer(&lb), la.cmp_memcmp_order(&lb));
    }

    /// The deployed comparator is the derived `Ord` on `[u16; 16]`; pin that equivalence so a
    /// re-implementation of `cmp_limb_lex` cannot silently diverge from `ExactTaggedKey`.
    #[test]
    fn limb_lex_is_exactly_derived_ord_on_the_limb_array() {
        let corpus = order_corpus();
        for a in &corpus {
            for b in &corpus {
                let (la, lb) = (Bytes32::new(*a).limbs(), Bytes32::new(*b).limbs());
                assert_eq!(la.cmp_limb_lex(&lb), la.as_u16s().cmp(lb.as_u16s()));
            }
        }
    }

    #[test]
    fn u64_limbs_round_trip_and_keep_place_order() {
        for v in [
            0u64,
            1,
            u64::MAX,
            0x0123_4567_89AB_CDEF,
            1 << 15,
            1 << 16,
            1 << 63,
        ] {
            assert_eq!(U64Limbs4::encode(v).decode(), v);
            let limbs = U64Limbs4::encode(v);
            let recomposed: u64 = limbs
                .as_u16s()
                .iter()
                .enumerate()
                .map(|(i, l)| u64::from(*l) << (16 * i))
                .sum();
            assert_eq!(recomposed, v, "value = sum limb_i * 2^(16 i) must hold");
        }
    }
}
