//! The adapter-defined vault lock-record account layout.
//!
//! GROUND TRUTH — this MUST be byte-identical to the dregg relayer's parser:
//! `bridge/src/solana_wire.rs:614-644`
//!   `LOCK_RECORD_LEN = 32 + 32 + 8 = 72`
//!   `data = lock_id(32) ‖ recipient(32) ‖ amount_le(8)`
//!   `encode_lock_record(lock_id:&[u8;32], recipient:&CellId, amount:u64) -> Vec<u8>`
//!   `decode_lock_record(&[u8]) -> Option<([u8;32], CellId, u64)>` (returns `None`
//!    unless `data.len() == 72`).
//!
//! If these 72 bytes are wrong in ANY position, `decode_lock_record` returns
//! `None` and the lock is unminable (see `bridge/src/solana_relayer.rs:698-701`,
//! `verify_finalized_account` → `RelayerError::NoLockRecord`). This module is the
//! Solana-side mirror of that contract and is exercised by a byte-identity test.

/// The number of bytes of the adapter-defined vault-lock record.
///
/// Mirror of `bridge/src/solana_wire.rs:615` `LOCK_RECORD_LEN`.
pub const LOCK_RECORD_LEN: usize = 32 + 32 + 8;

/// Encode the lock record into the vault-record account's `data`:
/// `lock_id(32) ‖ recipient(32) ‖ amount_le(8)`.
///
/// Byte-for-byte identical to `bridge/src/solana_wire.rs:623` `encode_lock_record`
/// (there `recipient` is a `CellId` whose `as_bytes()` is the same 32 raw bytes we
/// take here directly). The relayer's `decode_lock_record` is the inverse.
pub fn encode_lock_record(
    lock_id: &[u8; 32],
    recipient: &[u8; 32],
    amount: u64,
) -> [u8; LOCK_RECORD_LEN] {
    let mut d = [0u8; LOCK_RECORD_LEN];
    d[0..32].copy_from_slice(lock_id);
    d[32..64].copy_from_slice(recipient);
    d[64..72].copy_from_slice(&amount.to_le_bytes());
    d
}

/// Decode a vault-record account's `data` into `(lock_id, recipient, amount)`.
/// Returns `None` unless the data is EXACTLY the 72-byte lock-record layout.
///
/// This is the local inverse of [`encode_lock_record`] and matches the relayer's
/// `decode_lock_record` (`bridge/src/solana_wire.rs:633`). It is used by the
/// program's own fail-closed size check and by the round-trip test.
pub fn decode_lock_record(data: &[u8]) -> Option<([u8; 32], [u8; 32], u64)> {
    if data.len() != LOCK_RECORD_LEN {
        return None;
    }
    let mut lock_id = [0u8; 32];
    lock_id.copy_from_slice(&data[0..32]);
    let mut recipient = [0u8; 32];
    recipient.copy_from_slice(&data[32..64]);
    let mut amt = [0u8; 8];
    amt.copy_from_slice(&data[64..72]);
    Some((lock_id, recipient, u64::from_le_bytes(amt)))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ANTI-MIRROR CHECK. The Solana-side encoding must be byte-identical to the
    /// documented 72-byte layout `lock_id ‖ recipient ‖ amount_le`, or the dregg
    /// relayer's `decode_lock_record` (`solana_wire.rs:633`) returns `None` and the
    /// lock is unminable. This asserts the layout position-by-position — NOT via a
    /// round-trip through our own decoder (which would be self-consistent but could
    /// share a bug), but against the literal byte offsets the relayer reads.
    #[test]
    fn lock_record_is_byte_identical_to_72_byte_layout() {
        assert_eq!(
            LOCK_RECORD_LEN, 72,
            "relayer decode requires exactly 72 bytes"
        );

        let lock_id = [0x11u8; 32];
        let recipient = [0x22u8; 32];
        let amount: u64 = 0x0102_0304_0506_0708;

        let d = encode_lock_record(&lock_id, &recipient, amount);

        // exact length the relayer's `data.len() != LOCK_RECORD_LEN` gate checks
        assert_eq!(d.len(), 72);
        // [0..32] = lock_id, verbatim
        assert_eq!(&d[0..32], &lock_id);
        // [32..64] = recipient (the dregg CellId), verbatim
        assert_eq!(&d[32..64], &recipient);
        // [64..72] = amount, little-endian
        assert_eq!(&d[64..72], &amount.to_le_bytes());
        // full spelled-out expectation, so a reordering is caught even if two
        // fields happen to share a value
        assert_eq!(
            &d[64..72],
            &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01],
            "amount must be little-endian in bytes 64..72"
        );
    }

    #[test]
    fn decode_is_inverse_of_encode() {
        let lock_id = [0xABu8; 32];
        let recipient = [0xCDu8; 32];
        let amount: u64 = 42_000_000;
        let d = encode_lock_record(&lock_id, &recipient, amount);
        let (l, r, a) = decode_lock_record(&d).expect("72 bytes decodes");
        assert_eq!(l, lock_id);
        assert_eq!(r, recipient);
        assert_eq!(a, amount);
    }

    #[test]
    fn decode_rejects_wrong_length() {
        // the relayer refuses anything not exactly 72 bytes; so must we.
        assert!(decode_lock_record(&[0u8; 71]).is_none());
        assert!(decode_lock_record(&[0u8; 73]).is_none());
        assert!(decode_lock_record(&[]).is_none());
    }
}
