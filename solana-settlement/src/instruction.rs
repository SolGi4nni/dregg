//! Instruction set + wire encoding for the dregg Solana settlement program.
//!
//! Native dispatch: the first byte of `instruction_data` is the tag, the rest is
//! the tag's payload. Fail-closed: an unknown tag or a short/oversized payload is
//! rejected (`SettlementError::InvalidInstruction`) rather than defaulted.
//!
//! The `Settle` payload is the SAME proof shape as the EVM `settle` (gnark
//! `MarshalSolidity` words) and the `settlement_groth16.json` fixture:
//!   A (G1, 64) || B (G2, 128) || C (G1, 64) || commitment (G1, 64)
//!   || commitment_pok (G1, 64) || inputs (25 * 32-byte big-endian scalars).
//! The 25-lane statement (genesis || final || num_turns || chain_digest) is the
//! `inputs` vector itself -- the processor slices it, so there is nothing to
//! double-supply or disagree with (the EVM took the lanes separately and
//! cross-checked; here the inputs vector IS the statement).

use crate::error::SettlementError;
use crate::vk::NUM_PUBLIC_INPUTS;

/// 1-byte instruction tags.
pub const TAG_INIT: u8 = 0;
pub const TAG_SETTLE: u8 = 1;

const SETTLE_LEN: usize = 64 + 128 + 64 + 64 + 64 + NUM_PUBLIC_INPUTS * 32;
const INIT_LEN: usize = 8 * 4 + 32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SettlementInstruction {
    /// Pin the genesis anchor + the verifying-key hash, creating the program-owned
    /// settlement state account. The Solana twin of the EVM `DreggSettlement`
    /// constructor. Fail-closed: every genesis lane must be canonical, the VK hash
    /// must be non-zero.
    InitSettlement {
        genesis_root: [u32; 8],
        vk_hash: [u8; 32],
    },
    /// Submit a settlement: verify the Groth16 proof over the 25-lane statement and
    /// advance the proven root. The Solana twin of the EVM `settle`.
    Settle {
        a: [u8; 64],
        b: [u8; 128],
        c: [u8; 64],
        commitment: [u8; 64],
        commitment_pok: [u8; 64],
        inputs: [[u8; 32]; NUM_PUBLIC_INPUTS],
    },
}

fn take<const N: usize>(src: &[u8], off: &mut usize) -> [u8; N] {
    let mut out = [0u8; N];
    out.copy_from_slice(&src[*off..*off + N]);
    *off += N;
    out
}

impl SettlementInstruction {
    pub fn unpack(data: &[u8]) -> Result<Self, SettlementError> {
        let (&tag, rest) = data
            .split_first()
            .ok_or(SettlementError::InvalidInstruction)?;
        match tag {
            TAG_INIT => {
                if rest.len() != INIT_LEN {
                    return Err(SettlementError::InvalidInstruction);
                }
                let mut off = 0usize;
                let mut genesis_root = [0u32; 8];
                for l in genesis_root.iter_mut() {
                    *l = u32::from_be_bytes(take::<4>(rest, &mut off));
                }
                let vk_hash = take::<32>(rest, &mut off);
                Ok(Self::InitSettlement {
                    genesis_root,
                    vk_hash,
                })
            }
            TAG_SETTLE => {
                if rest.len() != SETTLE_LEN {
                    return Err(SettlementError::InvalidInstruction);
                }
                let mut off = 0usize;
                let a = take::<64>(rest, &mut off);
                let b = take::<128>(rest, &mut off);
                let c = take::<64>(rest, &mut off);
                let commitment = take::<64>(rest, &mut off);
                let commitment_pok = take::<64>(rest, &mut off);
                let mut inputs = [[0u8; 32]; NUM_PUBLIC_INPUTS];
                for slot in inputs.iter_mut() {
                    *slot = take::<32>(rest, &mut off);
                }
                Ok(Self::Settle {
                    a,
                    b,
                    c,
                    commitment,
                    commitment_pok,
                    inputs,
                })
            }
            _ => Err(SettlementError::InvalidInstruction),
        }
    }

    /// Serialize (used by clients / tests to build the instruction data).
    pub fn pack(&self) -> Vec<u8> {
        match self {
            Self::InitSettlement {
                genesis_root,
                vk_hash,
            } => {
                let mut d = Vec::with_capacity(1 + INIT_LEN);
                d.push(TAG_INIT);
                for l in genesis_root {
                    d.extend_from_slice(&l.to_be_bytes());
                }
                d.extend_from_slice(vk_hash);
                d
            }
            Self::Settle {
                a,
                b,
                c,
                commitment,
                commitment_pok,
                inputs,
            } => {
                let mut d = Vec::with_capacity(1 + SETTLE_LEN);
                d.push(TAG_SETTLE);
                d.extend_from_slice(a);
                d.extend_from_slice(b);
                d.extend_from_slice(c);
                d.extend_from_slice(commitment);
                d.extend_from_slice(commitment_pok);
                for s in inputs {
                    d.extend_from_slice(s);
                }
                d
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn init_roundtrip() {
        let i = SettlementInstruction::InitSettlement {
            genesis_root: [1, 2, 3, 4, 5, 6, 7, 8],
            vk_hash: [0x22; 32],
        };
        assert_eq!(SettlementInstruction::unpack(&i.pack()).unwrap(), i);
    }

    #[test]
    fn settle_roundtrip() {
        let i = SettlementInstruction::Settle {
            a: [1u8; 64],
            b: [2u8; 128],
            c: [3u8; 64],
            commitment: [4u8; 64],
            commitment_pok: [5u8; 64],
            inputs: [[7u8; 32]; NUM_PUBLIC_INPUTS],
        };
        assert_eq!(SettlementInstruction::unpack(&i.pack()).unwrap(), i);
    }

    #[test]
    fn rejects_short_settle() {
        let mut d = vec![TAG_SETTLE];
        d.extend_from_slice(&[0u8; 10]);
        assert_eq!(
            SettlementInstruction::unpack(&d),
            Err(SettlementError::InvalidInstruction)
        );
    }

    #[test]
    fn rejects_unknown_tag() {
        assert_eq!(
            SettlementInstruction::unpack(&[9u8, 0, 0]),
            Err(SettlementError::InvalidInstruction)
        );
    }
}
