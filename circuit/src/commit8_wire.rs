//! **THE ONE WIRE CODEC for a published 8-felt state-commit anchor.**
//!
//! A rotated wide leg publishes its BEFORE / AFTER state commitments as eight `BabyBear` lanes at
//! the PI tail, and `dregg_sdk::verify_full_turn_bound` takes those two octets as
//! `expected_old_commit` / `expected_new_commit`. Until 2026-08-07 the only party that ever held
//! those values outside the prover was the prover itself, so the one production surface that
//! re-verifies a served artifact (`discord-bot`'s `/proof turn`) read them **out of the artifact**
//! and handed them back — the two `CommitmentMismatch` teeth compared `x != x`.
//!
//! Closing that means a node **serving** the pair it derived at commit time, and a checker
//! **parsing** it. Those are two crates in two different cargo workspaces, so a hand-rolled
//! encoder on each side is precisely the twin this repo keeps finding. This module is the single
//! definition both call.
//!
//! # The encoding
//!
//! Lane `i` occupies bytes `[4i, 4i+4)` little-endian — **byte-identical to
//! [`crate::Faithful8::to_bytes32`]**, so a `[BabyBear; 8]` written here and a `Faithful8` written
//! there produce the same 32 bytes and a consumer can compare a served anchor against a
//! `TurnReceipt::pre_state_hash` without a second convention. The hex form is that byte string,
//! lowercase, 64 characters.
//!
//! ⚠ Deliberately NOT routed through [`crate::Faithful8`]: that type's constructor set is a WALL
//! (`faithful8`'s module docs), and a raw PI-tail octet read off a proof is exactly what must not
//! acquire a `Faithful8` by construction — it is a **claim**, not a faithful fold. The bytes agree;
//! the type does not, and that is the point.

use crate::field::BabyBear;

/// The canonical 32 bytes of a published 8-felt commit anchor (lane `i` → bytes `[4i, 4i+4)` LE).
#[inline]
pub fn commit8_to_bytes(lanes: &[BabyBear; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, lane) in lanes.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&lane.as_u32().to_le_bytes());
    }
    out
}

/// The inverse of [`commit8_to_bytes`].
///
/// ⚠ Every 4-byte group is reduced mod `p` by `BabyBear::new`, so a non-canonical group (a lane
/// `>= p`) decodes to a DIFFERENT octet than it encoded from. That is refused rather than
/// silently folded: a served anchor that does not round-trip is malformed, and accepting it would
/// let a server hand a checker two byte strings that compare equal after reduction.
#[inline]
pub fn commit8_from_bytes(b: &[u8; 32]) -> Option<[BabyBear; 8]> {
    let mut lanes = [BabyBear::ZERO; 8];
    for (i, lane) in lanes.iter_mut().enumerate() {
        let raw = u32::from_le_bytes([b[i * 4], b[i * 4 + 1], b[i * 4 + 2], b[i * 4 + 3]]);
        let felt = BabyBear::new(raw);
        if felt.as_u32() != raw {
            return None;
        }
        *lane = felt;
    }
    Some(lanes)
}

/// The 64-lowercase-hex-character form of [`commit8_to_bytes`].
#[inline]
pub fn commit8_to_hex(lanes: &[BabyBear; 8]) -> String {
    commit8_to_bytes(lanes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

/// Parse the [`commit8_to_hex`] form. `None` on anything that is not exactly 64 hex characters
/// decoding to a canonical octet — a malformed anchor is a REFUSAL, never a best-effort octet.
pub fn commit8_from_hex(s: &str) -> Option<[BabyBear; 8]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut bytes = [0u8; 32];
    for (i, b) in bytes.iter_mut().enumerate() {
        *b = u8::from_str_radix(s.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    commit8_from_bytes(&bytes)
}

/// The 64-byte wire/store form of a BEFORE ‖ AFTER anchor PAIR — the object a node persists beside
/// a finalized turn's proof and serves from `GET /api/turn/{hash}/anchor`.
#[inline]
pub fn commit8_pair_to_bytes(old: &[BabyBear; 8], new: &[BabyBear; 8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(&commit8_to_bytes(old));
    out[32..].copy_from_slice(&commit8_to_bytes(new));
    out
}

/// Parse the 64-byte pair. `None` on a wrong length or a non-canonical lane (fail-closed: a
/// truncated or corrupt store entry must not decode to a *different* pair that then gets served as
/// the value a stranger binds a proof against).
pub fn commit8_pair_from_bytes(bytes: &[u8]) -> Option<([BabyBear; 8], [BabyBear; 8])> {
    if bytes.len() != 64 {
        return None;
    }
    let old: [u8; 32] = bytes[..32].try_into().ok()?;
    let new: [u8; 32] = bytes[32..].try_into().ok()?;
    Some((commit8_from_bytes(&old)?, commit8_from_bytes(&new)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn octet(seed: u32) -> [BabyBear; 8] {
        let mut o = [BabyBear::ZERO; 8];
        for (i, l) in o.iter_mut().enumerate() {
            *l = BabyBear::new(seed.wrapping_mul(i as u32 + 1).wrapping_add(7));
        }
        o
    }

    #[test]
    fn the_octet_round_trips_through_both_forms() {
        let o = octet(0x0BAD_F00D);
        assert_eq!(commit8_from_bytes(&commit8_to_bytes(&o)), Some(o));
        assert_eq!(commit8_from_hex(&commit8_to_hex(&o)), Some(o));
        assert_eq!(commit8_to_hex(&o).len(), 64);
    }

    /// The bytes are the SAME bytes `Faithful8::to_bytes32` writes — that agreement is what lets a
    /// served anchor be compared against a receipt's `pre_state_hash` with no second convention.
    #[test]
    fn the_bytes_agree_with_faithful8() {
        let b = [0x5Au8; 32];
        let f = crate::Faithful8::from_bytes32(&b);
        assert_eq!(commit8_to_bytes(&f.limbs()), f.to_bytes32());
    }

    #[test]
    fn the_pair_round_trips_and_a_short_entry_is_refused() {
        let (a, b) = (octet(3), octet(11));
        let enc = commit8_pair_to_bytes(&a, &b);
        assert_eq!(commit8_pair_from_bytes(&enc), Some((a, b)));
        assert_eq!(commit8_pair_from_bytes(&enc[..63]), None);
        assert_eq!(commit8_pair_from_bytes(&[]), None);
    }

    /// A NON-CANONICAL lane (>= p) is refused rather than reduced — otherwise two different served
    /// hex strings would decode to one octet and a checker's comparison would accept both.
    #[test]
    fn a_non_canonical_lane_is_refused_not_reduced() {
        let mut bytes = [0u8; 32];
        // p = 2^31 - 2^27 + 1 = 0x78000001; 0xFFFF_FFFF is far above it.
        bytes[..4].copy_from_slice(&0xFFFF_FFFFu32.to_le_bytes());
        assert_eq!(commit8_from_bytes(&bytes), None);
        let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(commit8_from_hex(&hex), None);
    }

    #[test]
    fn a_malformed_hex_string_is_refused() {
        assert_eq!(commit8_from_hex("zz"), None);
        assert_eq!(commit8_from_hex(&"ab".repeat(31)), None);
        assert_eq!(commit8_from_hex(&"zz".repeat(32)), None);
    }
}
