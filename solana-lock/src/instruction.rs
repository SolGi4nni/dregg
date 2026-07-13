//! Instruction set + wire encoding for the dregg Solana lock program.
//!
//! Native dispatch: the first byte of `instruction_data` is the tag, the rest is
//! the tag's payload. Fail-closed: an unknown tag or a short/oversized payload is
//! rejected (`LockError::InvalidInstruction`) rather than defaulted.

use crate::error::LockError;
use crate::state::MAX_ORACLE_KEYS;

/// 1-byte instruction tags.
pub const TAG_INIT_VAULT: u8 = 0;
pub const TAG_LOCK: u8 = 1;
pub const TAG_UNLOCK: u8 = 2;
/// Escrow (timeout/refund) surface — the two-branch, exactly-once DrEX routing-safety
/// twin of the EVM `DreggVault` escrow.
pub const TAG_ESCROW_LOCK: u8 = 3;
pub const TAG_ESCROW_RELEASE: u8 = 4;
pub const TAG_ESCROW_REFUND: u8 = 5;

/// The parsed, validated instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LockInstruction {
    /// Create the program-owned vault (config PDA + SPL token vault account whose
    /// SPL authority is the vault-authority PDA). The unlock trust boundary is an
    /// **M-of-N ed25519 oracle key-set**: `oracle_threshold` (M) valid signatures
    /// from DISTINCT `oracle_keys` (N) over the canonical unlock message hash are
    /// required to release funds (see [`LockInstruction::Unlock`] and
    /// [`crate::attestation`]). Fail-closed: `1 <= M <= N <= MAX_ORACLE_KEYS`.
    InitVault {
        oracle_threshold: u8,
        oracle_keys: Vec<[u8; 32]>,
    },
    /// Lock `amount` of $DREGG for the dregg cell `dregg_recipient`. Transfers the
    /// tokens into the vault and writes a fresh 72-byte lock record. THE mint path.
    Lock {
        amount: u64,
        dregg_recipient: [u8; 32],
    },
    /// Release `amount` of $DREGG from the vault to the recipient token account,
    /// authorized by a threshold of oracle-set ed25519 signatures over the canonical
    /// unlock message hash of `SolanaUnlockRequest { spl_mint = config.mint, amount,
    /// solana_recipient = recipient token account, redeem_id }`. `redeem_id` is also
    /// the replay nonce (a redeem-receipt PDA keyed by it must not already exist).
    /// The signatures ride in ed25519 native-program instructions in the same
    /// transaction — the wire args are unchanged from v1.
    Unlock { amount: u64, redeem_id: [u8; 32] },

    /// ESCROW LOCK — escrow `amount` of $DREGG into a per-escrow vault under
    /// `escrow_id`, reclaimable after `deadline` (unix seconds) if no DrEX fill
    /// clears it. The disjoint timed-escrow analog of [`Self::Lock`].
    EscrowLock {
        amount: u64,
        deadline: i64,
        escrow_id: [u8; 32],
    },
    /// ESCROW RELEASE — pay a locked escrow to the ring-matched recipient, authorized
    /// by an M-of-N oracle attestation over `unlock_message_hash(mint, amount,
    /// recipient, escrow_id)` (escrow_id doubles as the attestation's redeem/nonce).
    /// Terminal: the escrow record moves to `Released`.
    EscrowRelease { amount: u64, escrow_id: [u8; 32] },
    /// ESCROW REFUND — after the deadline, the depositor reclaims a locked escrow to
    /// its captured refund destination. No attestation (the timeout is the
    /// condition). Terminal: the escrow record moves to `Refunded`.
    EscrowRefund { escrow_id: [u8; 32] },
}

impl LockInstruction {
    /// Parse `data` (tag byte ‖ payload). Every arm checks its exact payload
    /// length; anything else is `InvalidInstruction`.
    pub fn unpack(data: &[u8]) -> Result<Self, LockError> {
        let (&tag, rest) = data.split_first().ok_or(LockError::InvalidInstruction)?;
        match tag {
            TAG_INIT_VAULT => {
                // payload: threshold(1) ‖ count(1) ‖ keys(count * 32)
                if rest.len() < 2 {
                    return Err(LockError::InvalidInstruction);
                }
                let oracle_threshold = rest[0];
                let count = rest[1] as usize;
                if count == 0 || count > MAX_ORACLE_KEYS {
                    return Err(LockError::InvalidInstruction);
                }
                // exact length: no trailing junk, no short buffer.
                if rest.len() != 2 + count * 32 {
                    return Err(LockError::InvalidInstruction);
                }
                let mut oracle_keys = Vec::with_capacity(count);
                for i in 0..count {
                    let mut k = [0u8; 32];
                    let off = 2 + i * 32;
                    k.copy_from_slice(&rest[off..off + 32]);
                    oracle_keys.push(k);
                }
                // threshold sanity here too (state re-validates on pack): 1 <= M <= N.
                if oracle_threshold == 0 || oracle_threshold as usize > count {
                    return Err(LockError::InvalidInstruction);
                }
                Ok(Self::InitVault {
                    oracle_threshold,
                    oracle_keys,
                })
            }
            TAG_LOCK => {
                if rest.len() != 8 + 32 {
                    return Err(LockError::InvalidInstruction);
                }
                let amount = read_u64_le(rest, 0)?;
                let dregg_recipient = read_array32(rest, 8, 8 + 32)?;
                Ok(Self::Lock {
                    amount,
                    dregg_recipient,
                })
            }
            TAG_UNLOCK => {
                if rest.len() != 8 + 32 {
                    return Err(LockError::InvalidInstruction);
                }
                let amount = read_u64_le(rest, 0)?;
                let redeem_id = read_array32(rest, 8, 8 + 32)?;
                Ok(Self::Unlock { amount, redeem_id })
            }
            TAG_ESCROW_LOCK => {
                // amount(8) ‖ deadline_i64(8) ‖ escrow_id(32)
                if rest.len() != 8 + 8 + 32 {
                    return Err(LockError::InvalidInstruction);
                }
                let amount = read_u64_le(rest, 0)?;
                let deadline = read_i64_le(rest, 8)?;
                let escrow_id = read_array32(rest, 16, 16 + 32)?;
                Ok(Self::EscrowLock {
                    amount,
                    deadline,
                    escrow_id,
                })
            }
            TAG_ESCROW_RELEASE => {
                if rest.len() != 8 + 32 {
                    return Err(LockError::InvalidInstruction);
                }
                let amount = read_u64_le(rest, 0)?;
                let escrow_id = read_array32(rest, 8, 8 + 32)?;
                Ok(Self::EscrowRelease { amount, escrow_id })
            }
            TAG_ESCROW_REFUND => {
                if rest.len() != 32 {
                    return Err(LockError::InvalidInstruction);
                }
                let escrow_id = read_array32(rest, 0, 32)?;
                Ok(Self::EscrowRefund { escrow_id })
            }
            _ => Err(LockError::InvalidInstruction),
        }
    }

    /// Serialize (used by clients / tests to build the instruction data).
    pub fn pack(&self) -> Vec<u8> {
        match self {
            Self::InitVault {
                oracle_threshold,
                oracle_keys,
            } => {
                let mut d = Vec::with_capacity(1 + 2 + oracle_keys.len() * 32);
                d.push(TAG_INIT_VAULT);
                d.push(*oracle_threshold);
                d.push(oracle_keys.len() as u8);
                for k in oracle_keys {
                    d.extend_from_slice(k);
                }
                d
            }
            Self::Lock {
                amount,
                dregg_recipient,
            } => {
                let mut d = Vec::with_capacity(1 + 8 + 32);
                d.push(TAG_LOCK);
                d.extend_from_slice(&amount.to_le_bytes());
                d.extend_from_slice(dregg_recipient);
                d
            }
            Self::Unlock { amount, redeem_id } => {
                let mut d = Vec::with_capacity(1 + 8 + 32);
                d.push(TAG_UNLOCK);
                d.extend_from_slice(&amount.to_le_bytes());
                d.extend_from_slice(redeem_id);
                d
            }
            Self::EscrowLock {
                amount,
                deadline,
                escrow_id,
            } => {
                let mut d = Vec::with_capacity(1 + 8 + 8 + 32);
                d.push(TAG_ESCROW_LOCK);
                d.extend_from_slice(&amount.to_le_bytes());
                d.extend_from_slice(&deadline.to_le_bytes());
                d.extend_from_slice(escrow_id);
                d
            }
            Self::EscrowRelease { amount, escrow_id } => {
                let mut d = Vec::with_capacity(1 + 8 + 32);
                d.push(TAG_ESCROW_RELEASE);
                d.extend_from_slice(&amount.to_le_bytes());
                d.extend_from_slice(escrow_id);
                d
            }
            Self::EscrowRefund { escrow_id } => {
                let mut d = Vec::with_capacity(1 + 32);
                d.push(TAG_ESCROW_REFUND);
                d.extend_from_slice(escrow_id);
                d
            }
        }
    }
}

fn read_i64_le(data: &[u8], off: usize) -> Result<i64, LockError> {
    let end = off + 8;
    if data.len() < end {
        return Err(LockError::InvalidInstruction);
    }
    let mut b = [0u8; 8];
    b.copy_from_slice(&data[off..end]);
    Ok(i64::from_le_bytes(b))
}

fn read_u64_le(data: &[u8], off: usize) -> Result<u64, LockError> {
    let end = off + 8;
    if data.len() < end {
        return Err(LockError::InvalidInstruction);
    }
    let mut b = [0u8; 8];
    b.copy_from_slice(&data[off..end]);
    Ok(u64::from_le_bytes(b))
}

/// Read a `[u8;32]` from `data[off..end]`, requiring `data.len() == end` so trailing
/// junk is rejected.
fn read_array32(data: &[u8], off: usize, end: usize) -> Result<[u8; 32], LockError> {
    if data.len() != end || end - off != 32 {
        return Err(LockError::InvalidInstruction);
    }
    let mut b = [0u8; 32];
    b.copy_from_slice(&data[off..end]);
    Ok(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_all_tags() {
        for ix in [
            LockInstruction::InitVault {
                oracle_threshold: 2,
                oracle_keys: vec![[7u8; 32], [8u8; 32], [9u8; 32]],
            },
            LockInstruction::Lock {
                amount: 123,
                dregg_recipient: [9u8; 32],
            },
            LockInstruction::Unlock {
                amount: 456,
                redeem_id: [3u8; 32],
            },
        ] {
            let packed = ix.pack();
            assert_eq!(LockInstruction::unpack(&packed).unwrap(), ix);
        }
    }

    #[test]
    fn empty_data_rejected() {
        assert_eq!(
            LockInstruction::unpack(&[]),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn unknown_tag_rejected() {
        assert_eq!(
            LockInstruction::unpack(&[0xFF]),
            Err(LockError::InvalidInstruction)
        );
        assert_eq!(
            LockInstruction::unpack(&[3, 0, 0]),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn short_lock_rejected() {
        // tag=1 with only 7 payload bytes (needs 40)
        let mut d = vec![TAG_LOCK];
        d.extend_from_slice(&[0u8; 7]);
        assert_eq!(
            LockInstruction::unpack(&d),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn oversized_lock_rejected() {
        // tag=1 with 41 payload bytes (one too many)
        let mut d = vec![TAG_LOCK];
        d.extend_from_slice(&[0u8; 41]);
        assert_eq!(
            LockInstruction::unpack(&d),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn short_init_rejected() {
        // tag + threshold + count=2 but only one key's worth of bytes follows.
        let mut d = vec![TAG_INIT_VAULT, 1u8, 2u8];
        d.extend_from_slice(&[0u8; 32]);
        assert_eq!(
            LockInstruction::unpack(&d),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn init_zero_count_rejected() {
        // count = 0 (empty oracle set) — NOMAD-LAW, refused at parse.
        assert_eq!(
            LockInstruction::unpack(&[TAG_INIT_VAULT, 0u8, 0u8]),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn init_zero_threshold_rejected() {
        // count = 1, threshold = 0 — NOMAD-LAW, refused at parse.
        let mut d = vec![TAG_INIT_VAULT, 0u8, 1u8];
        d.extend_from_slice(&[5u8; 32]);
        assert_eq!(
            LockInstruction::unpack(&d),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn init_threshold_gt_count_rejected() {
        // count = 1, threshold = 2 (> N).
        let mut d = vec![TAG_INIT_VAULT, 2u8, 1u8];
        d.extend_from_slice(&[5u8; 32]);
        assert_eq!(
            LockInstruction::unpack(&d),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn init_oversized_count_rejected() {
        // count exceeds MAX_ORACLE_KEYS.
        let d = vec![TAG_INIT_VAULT, 1u8, (MAX_ORACLE_KEYS + 1) as u8];
        assert_eq!(
            LockInstruction::unpack(&d),
            Err(LockError::InvalidInstruction)
        );
    }

    #[test]
    fn amount_is_little_endian() {
        let ix = LockInstruction::Lock {
            amount: 0x0102_0304_0506_0708,
            dregg_recipient: [0u8; 32],
        };
        let d = ix.pack();
        // byte 0 = tag, bytes 1..9 = amount LE
        assert_eq!(&d[1..9], &[0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);
    }
}
