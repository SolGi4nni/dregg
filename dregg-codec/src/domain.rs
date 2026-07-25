//! **The domain-tag registry.** One place where separation tags are minted, so two unrelated
//! commitments cannot silently share one.
//!
//! The convention already in the tree: four ASCII characters packed **big-endian** into a `u32`,
//! the last character a version digit — `"FNC2" = 0x464e_4332`. That reading is fixed here and
//! mirrored by tests against the values the deployed sites already use, so a rename in either
//! direction is caught rather than absorbed.
//!
//! A tag must be `< p`, since it is absorbed as a felt and a reduction would alias two tags
//! together. [`Domain::from_ascii`] is a `const fn` that panics at compile time on a tag that
//! would need reducing, so an out-of-range tag can never reach a trace.

use serde::{Deserialize, Serialize};

use crate::limbs::BABYBEAR_P;

/// A domain-separation tag: one felt, absorbed ahead of the value it separates.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Domain(u32);

impl Domain {
    /// Mint a tag from four ASCII characters, read big-endian.
    ///
    /// # Panics
    /// If the resulting `u32` is not `< p`. In a `const` context this is a compile-time error,
    /// which is the point: the check cannot be skipped and the failure cannot be a silent alias.
    #[must_use]
    pub const fn from_ascii(tag: [u8; 4]) -> Self {
        let v = u32::from_be_bytes(tag);
        assert!(
            v < BABYBEAR_P,
            "domain tag does not fit in BabyBear; it would alias with tag - p"
        );
        Self(v)
    }

    /// The tag as a felt value. Always `< p` by construction, so no reduction occurs.
    #[must_use]
    pub const fn felt(self) -> u32 {
        self.0
    }

    // ── Mirrors of tags already deployed. These are protocol ABI: the numeric values are
    // pinned by test against the sites that own them, they are not free to change here. ──

    /// `FNC2` — faithful note commitment v2 (`cell::note::FAITHFUL_NOTE_COMMIT_DOMAIN_V2`,
    /// Lean `NOTE_COMMITMENT_V2_DOMAIN`).
    pub const NOTE_COMMITMENT_V2: Self = Self::from_ascii(*b"FNC2");
    /// `FNF2` — faithful note nullifier v2.
    pub const NOTE_NULLIFIER_V2: Self = Self::from_ascii(*b"FNF2");
    /// `FNO2` — faithful note owner/address v2.
    pub const NOTE_OWNER_V2: Self = Self::from_ascii(*b"FNO2");
    /// `CPL2` — exact cap-tree leaf (`circuit::exact_cap_root::EXACT_CAP_LEAF_DOMAIN`).
    pub const EXACT_CAP_LEAF: Self = Self::from_ascii(*b"CPL2");
    /// `FNI2` — exact linked-list leaf of the AAFI nullifier accumulator.
    pub const EXACT_LINKED_LEAF: Self = Self::from_ascii(*b"FNI2");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ABI pin. These numbers are what the deployed sites already absorb; the registry mirrors
    /// them and must not drift. If one of these fails, the registry moved, not the protocol.
    #[test]
    fn deployed_tag_values_are_pinned() {
        assert_eq!(Domain::NOTE_COMMITMENT_V2.felt(), 0x464e_4332);
        assert_eq!(Domain::NOTE_NULLIFIER_V2.felt(), 0x464e_4632);
        assert_eq!(Domain::NOTE_OWNER_V2.felt(), 0x464e_4f32);
        assert_eq!(Domain::EXACT_CAP_LEAF.felt(), 0x4350_4c32);
        assert_eq!(Domain::EXACT_LINKED_LEAF.felt(), 0x464e_4932);
    }

    #[test]
    fn every_registered_tag_is_a_canonical_felt() {
        for d in [
            Domain::NOTE_COMMITMENT_V2,
            Domain::NOTE_NULLIFIER_V2,
            Domain::NOTE_OWNER_V2,
            Domain::EXACT_CAP_LEAF,
            Domain::EXACT_LINKED_LEAF,
        ] {
            assert!(d.felt() < BABYBEAR_P);
        }
    }

    /// Distinctness is the only property a separation tag actually has to have.
    #[test]
    fn registered_tags_are_pairwise_distinct() {
        let all = [
            Domain::NOTE_COMMITMENT_V2,
            Domain::NOTE_NULLIFIER_V2,
            Domain::NOTE_OWNER_V2,
            Domain::EXACT_CAP_LEAF,
            Domain::EXACT_LINKED_LEAF,
        ];
        for (i, a) in all.iter().enumerate() {
            for b in &all[i + 1..] {
                assert_ne!(a, b);
            }
        }
    }

    #[test]
    fn ascii_is_read_big_endian() {
        assert_eq!(Domain::from_ascii(*b"FNC2").felt(), 0x464e_4332);
        assert_ne!(Domain::from_ascii(*b"FNC2").felt(), 0x3234_4e46);
    }
}
