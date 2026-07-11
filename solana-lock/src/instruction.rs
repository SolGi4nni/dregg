//! Instruction set + wire encoding for the dregg Solana lock program.
//!
//! Native dispatch: the first byte of `instruction_data` is the tag, the rest is
//! the tag's payload. Fail-closed: an unknown tag or a short/oversized payload is
//! rejected (`LockError::InvalidInstruction`) rather than defaulted.

use crate::error::LockError;

/// 1-byte instruction tags.
pub const TAG_INIT_VAULT: u8 = 0;
pub const TAG_LOCK: u8 = 1;
pub const TAG_UNLOCK: u8 = 2;

/// The parsed, validated instruction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LockInstruction {
    /// Create the program-owned vault (config PDA + SPL token vault account whose
    /// SPL authority is the vault-authority PDA). `unlock_authority` is the ed25519
    /// pubkey permitted to sign [`LockInstruction::Unlock`] (the bridge authority;
    /// a real deployment gates this on a dregg burn-attestation — see the residual
    /// note in `lib.rs`).
    InitVault { unlock_authority: [u8; 32] },
    /// Lock `amount` of $DREGG for the dregg cell `dregg_recipient`. Transfers the
    /// tokens into the vault and writes a fresh 72-byte lock record. THE mint path.
    Lock {
        amount: u64,
        dregg_recipient: [u8; 32],
    },
    /// Release `amount` of $DREGG from the vault to the recipient token account,
    /// authorized by `unlock_authority`. `redeem_id` is the replay nonce (a
    /// redeem-receipt PDA keyed by it must not already exist).
    Unlock { amount: u64, redeem_id: [u8; 32] },
}

impl LockInstruction {
    /// Parse `data` (tag byte ‖ payload). Every arm checks its exact payload
    /// length; anything else is `InvalidInstruction`.
    pub fn unpack(data: &[u8]) -> Result<Self, LockError> {
        let (&tag, rest) = data.split_first().ok_or(LockError::InvalidInstruction)?;
        match tag {
            TAG_INIT_VAULT => {
                let unlock_authority = read_array32(rest, 0, 32)?;
                Ok(Self::InitVault { unlock_authority })
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
            _ => Err(LockError::InvalidInstruction),
        }
    }

    /// Serialize (used by clients / tests to build the instruction data).
    pub fn pack(&self) -> Vec<u8> {
        match self {
            Self::InitVault { unlock_authority } => {
                let mut d = Vec::with_capacity(1 + 32);
                d.push(TAG_INIT_VAULT);
                d.extend_from_slice(unlock_authority);
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
        }
    }
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
                unlock_authority: [7u8; 32],
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
        let mut d = vec![TAG_INIT_VAULT];
        d.extend_from_slice(&[0u8; 31]);
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
