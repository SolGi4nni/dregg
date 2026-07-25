//! **THE canonical byte→felt codec.** One designation, replacing ~17 local re-inventions.
//!
//! Plan of record: `docs/DESIGN-canonical-byte-felt-codec.md`. This crate is that document's
//! Stage 0: it is **additive**, it moves **zero bytes**, and it closes zero wounds by itself.
//! Its job is to exist so that everything after it has one thing to point at.
//!
//! # The two layers, because injectivity and binding are different requirements
//!
//! **Layer L — [`Limbs16`].** Sixteen little-endian `u16` limbs. Injective by construction:
//! `2^16 ≪ p`, so no modular reduction happens and the inverse is a `memcpy`. Use it wherever the
//! value must be **recoverable, ordered, or range-checked** — sorted-map addresses, AAFI brackets,
//! lex comparators, hash preimages, witness columns. In-AIR canonicity is 16 lookups at 16 bits,
//! the cheapest lookup width available, and the Lean emit already builds exactly that plan
//! (`u16Ranges`, `metatheory/Dregg2/Circuit/Emit/FaithfulNoteSpendDescriptorPlan.lean`).
//!
//! **Layer D — [`Digest8`].** The Poseidon2 squeeze over those limbs, eight felts wide. **Not**
//! injective — nothing eight felts wide can be, see below — but **hard**: birthday over `p^8`,
//! i.e. `2^123.63`, against the `O(1)` of the encodings it replaces. Use it wherever a value must
//! be **bound in a fixed-width committed slot**.
//!
//! ## There is no injective 8-felt encoding. Pigeonhole, not an engineering gap.
//!
//! `p = 2^31 − 2^27 + 1 = 2013265921`, so `log2(p) = 30.906891` and `p^8 ≈ 2^247.2551 < 2^256`.
//! The codomain is 8.75 bits too small; 99.77% of all 32-byte strings must participate in a
//! collision. Minimum injective width is `ceil(256 / 30.906891) = 9` felts. This is why the
//! failing sites in the wound catalogue do **not** fail for being non-injective — [`Digest8`] is
//! non-injective too and is fine. They fail because they are raw non-injective **projections**
//! (free, constructible collisions) where a **hard** non-injective **compression** was required.
//!
//! ## Endianness: little-endian. One rule, no exceptions.
//!
//! Four independent implementations of Layer L existed and they were not all the same map; three
//! were LE (including the deployed one, `exact_nullifier_aafi::raw_to_u16_le`) and one was BE.
//! LE wins: three of four, the deployed one, and Lean's stated convention (*"Every multi-limb
//! integer/byte string is little-endian"*). Integers keep place order too:
//! `u64 → 4 × u16` LE, `value = Σ limbᵢ · 2^16ⁱ` ([`U64Limbs4`]).
//!
//! The BE choice was **not** arbitrary — it bought byte order — and it gets an explicit answer
//! rather than a reversal. But the design document's answer is **wrong**, and correcting it is one
//! of this crate's deliverables. §2.5 claims a lex comparator over LE limbs "reads indices `15..0`
//! instead of `0..15`", recovering `memcmp` at "zero constraint cost". Index reversal recovers the
//! **little-endian-integer** order, not `memcmp`; `memcmp` compares byte 0 first and byte 0 is the
//! *low half* of limb 0, so recovering it costs a per-limb byte swap. And the **deployed**
//! comparator is neither: `exact_nullifier_aafi::ExactTaggedKey` uses the derived `Ord` on
//! `[u16; 16]` — lex over `0..15`, numeric per limb — which its own Lean KAT documents as
//! disagreeing with byte order. All three orders are therefore named separately and priced
//! separately: [`Limbs16::cmp_limb_lex`] (deployed, free), [`Limbs16::cmp_le_integer`] (free),
//! [`Limbs16::cmp_memcmp_order`] (**not** free). A test pins them as mutually distinct on the
//! AAFI's own KAT vector so the next copy cannot conflate them.
//!
//! # What this crate deliberately does NOT do
//!
//! It does not contain a field type, a permutation, or a constraint. **AIR is authored in Lean.**
//! The in-circuit half of this codec — the 16-bit range plans and the `Digest8 ↔ Limbs16`
//! canonicity gate (`Pack8Plan` / `packBodiesAt`, six constraints per lane, 48 per octet) —
//! already exists in Lean and is `#guard`-checked. Nothing here re-authors it, and nothing here
//! may be used at a constrained boundary before its Lean twin is emitted; see [`digest`].

pub mod digest;
pub mod domain;
pub mod limbs;

pub use digest::{Digest8, Squeeze8};
pub use domain::Domain;
pub use limbs::{
    BABYBEAR_P, BYTES32_U16_LIMBS, Bytes32, LIMB_BITS, Limbs16, U64_U16_LIMBS, U64Limbs4,
};
