//! The canonical Path of Angels Dark Bazaar receipt-digest wire type.
//!
//! ⚑ **The `receipt8-v2` proof family that used to live here is DELETED**
//! (2026-08-05). It proved the v1 fixed N=4/K=4 private clearing relation and
//! published one additional value — the canonical PoA transition receipt digest
//! as eight independent BabyBear lanes, at trace columns 181..188, public
//! inputs 12..19. Those eight columns appeared in no gate body, no boundary
//! body and no lookup tuple; `scripts/check-descriptor-anchor-inertness.py`
//! measured eight decorative anchors, and the family's own Lean docblock said
//! so plainly: *"These eight pins bind a proof transcript to a receipt
//! identity; they do not by themselves prove that the receipt is the output of
//! the PoA state machine. The consumer must run the Lean public-transition
//! judge … and compare all eight canonical lanes to these PIs."*
//!
//! The anchoring mechanism that repaired the settlement family does NOT
//! transfer here, and that is why this is a deletion rather than a rewrite. A
//! chip-derived anchor works by making a published value the image of rows the
//! proof exhibits — but v2's entire public surface beyond those eight lanes is
//! the v1 statement, which is already published and already chip-derived. An
//! anchor over it would be a function of values the verifier already holds:
//! redundancy dressed as a binding, which is worse than nothing because the
//! next reader would trust it.
//!
//! The receipt digest itself is not derivable in any of these AIRs — it hashes
//! a canonical JSON string (`DarkBazaarJudgeWire.digestString`) — so the honest
//! disposition of a family whose only reason to exist was publishing it is to
//! stop. Everything v2 offered is available from
//! [`crate::dark_bazaar_private`] plus the host-side judge comparison the v2
//! docblock already required, and
//! [`crate::dark_bazaar_private_poa_settlement`] supersedes it outright with a
//! settlement anchor the AIR actually forces.
//!
//! What survives is the wire type, which is a faithful decoder for Lean's
//! `Digest32` and is used by the settlement family to carry the four judge
//! digests it checks host-side.

use dregg_circuit::field::BABYBEAR_P;

use crate::dark_bazaar_private::DIGEST_WIDTH;

/// Canonical eight-lane representation of Lean's `Digest32` receipt output.
///
/// Lean's Dark Bazaar wire uses `V1.digestOfRoot`: eight canonical BabyBear
/// representatives, each serialized as one little-endian `u32`. The inner
/// array is private so construction always checks all eight representatives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PoaReceiptDigest([u32; DIGEST_WIDTH]);

impl PoaReceiptDigest {
    /// Decode the exact 32-byte Lean wire. Values at or above the BabyBear
    /// modulus refuse; silently applying `% p` would create aliases.
    pub fn try_from_lean_bytes(bytes: [u8; 32]) -> Result<Self, String> {
        let mut lanes = [0u32; DIGEST_WIDTH];
        for (lane, chunk) in bytes.chunks_exact(4).enumerate() {
            let value = u32::from_le_bytes(
                chunk
                    .try_into()
                    .expect("chunks_exact(4) always yields four bytes"),
            );
            if value >= BABYBEAR_P {
                return Err(format!(
                    "PoA receipt lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
            lanes[lane] = value;
        }
        Ok(Self(lanes))
    }

    pub const fn lanes(self) -> [u32; DIGEST_WIDTH] {
        self.0
    }

    pub fn to_lean_bytes(self) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for (lane, value) in self.0.into_iter().enumerate() {
            bytes[4 * lane..4 * lane + 4].copy_from_slice(&value.to_le_bytes());
        }
        bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(seed: u32) -> [u8; 32] {
        let mut bytes = [0u8; 32];
        for lane in 0..DIGEST_WIDTH {
            bytes[4 * lane..4 * lane + 4].copy_from_slice(&(seed + lane as u32).to_le_bytes());
        }
        bytes
    }

    #[test]
    fn receipt_wire_is_exact_little_endian_and_refuses_reduction_aliases() {
        let mut bytes = digest(1);
        bytes[0..4].copy_from_slice(&0x1020_3040u32.to_le_bytes());
        let receipt = PoaReceiptDigest::try_from_lean_bytes(bytes).expect("canonical lanes");
        assert_eq!(receipt.to_lean_bytes(), bytes);
        assert_eq!(receipt.lanes()[0], 0x1020_3040);

        let mut alias = bytes;
        alias[0..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(PoaReceiptDigest::try_from_lean_bytes(alias).is_err());
    }
}
