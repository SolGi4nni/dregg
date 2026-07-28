//! Instruction set + wire encoding for the dregg Solana settlement program.
//!
//! Native dispatch: the first byte of `instruction_data` is the tag, the rest is
//! the tag's payload. Fail-closed: an unknown tag or a short/oversized payload is
//! rejected (`SettlementError::InvalidInstruction`) rather than defaulted.
//!
//! The `Settle` payload is the SAME proof shape as the EVM `settle` (gnark
//! `MarshalSolidity` words) and the `settlement_groth16.json` fixture:
//!   A (G1, 64) || B (G2, 128) || C (G1, 64) || commitment (G1, 64)
//!   || commitment_pok (G1, 64) || lanes (25 * 4-byte big-endian u32).
//! The 25-lane statement (genesis || final || num_turns || chain_digest) is the
//! `lanes` vector itself -- the processor slices it, so there is nothing to
//! double-supply or disagree with (the EVM took the lanes separately and
//! cross-checked; here the lanes vector IS the statement).
//!
//! ## ⚑ WIRE FLAG DAY 2026-07-28: the lanes are u32, not 32-byte scalars
//!
//! `Settle` carried its 25 statement lanes as full 32-byte big-endian Groth16
//! scalars: 800 bytes, of which the processor REQUIRED 700 to be zero
//! (`input_to_lane` rejected any input with a non-zero high 28 bytes, because a
//! settlement lane is a canonical BabyBear residue `< 2^31`). Those 700 bytes made
//! the settle transaction **1495 serialized bytes against `PACKET_DATA_SIZE` =
//! 1232**, so a validator DROPPED it and the Solana settle could never be
//! broadcast at all -- measured by
//! `tests/settle_flow.rs::settle_transaction_fits_in_a_solana_packet`.
//!
//! Carrying the lanes as the `u32`s they provably are costs 100 bytes instead of
//! 800 and puts the transaction at 795 bytes. This is not a compression and not a
//! trade: it deletes bytes the program already proved were zero, and it NARROWS
//! what the wire can express (a non-canonical scalar is now unrepresentable rather
//! than merely rejected). The processor zero-extends each lane back to the 32-byte
//! scalar the BN254 MSM consumes.
//!
//! **What breaks:** `SETTLE_LEN` 1184 -> 484, so any client packing the old shape
//! is refused with `InvalidInstruction` (it does not reinterpret -- the length
//! check is exact). `SettlementInstruction::Settle`'s field is renamed
//! `inputs` -> `lanes` and retyped `[[u8; 32]; 25]` -> `[u32; 25]` so every
//! in-tree caller fails to COMPILE rather than silently packing 800 bytes.

use crate::error::SettlementError;
use crate::vk::NUM_PUBLIC_INPUTS;

/// 1-byte instruction tags.
pub const TAG_INIT: u8 = 0;
pub const TAG_SETTLE: u8 = 1;
pub const TAG_ASSERT_PROVEN_ROOT: u8 = 2;

/// Settle payload length: A || B || C || commitment || commitment_pok || 25 u32
/// lanes. 484 bytes (was 1184 when the lanes were 32-byte scalars).
pub const SETTLE_LEN: usize = 64 + 128 + 64 + 64 + 64 + NUM_PUBLIC_INPUTS * 4;
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
    ///
    /// `lanes` is the statement in the pinned order genesis[0..8) || final[8..16)
    /// || num_turns[16] || chain_digest[17..25), each a canonical BabyBear residue
    /// carried as a 4-byte big-endian u32 (see the module docs for why it is not a
    /// 32-byte scalar).
    Settle {
        a: [u8; 64],
        b: [u8; 128],
        c: [u8; 64],
        commitment: [u8; 64],
        commitment_pok: [u8; 64],
        lanes: [u32; NUM_PUBLIC_INPUTS],
    },
    /// Assert `root` (a `packLanes` key) is a dregg-proven root -- the CPI-able
    /// Solana `isProvenRoot` gate (the `DreggProofISM` analog). Succeeds iff the
    /// passed marker account is the registry PDA for `root`, is program-owned, and
    /// carries a valid marker; reverts otherwise (THE NOMAD LAW: a zero/default/
    /// unrecorded root has no marker and is refused). A consumer program CPIs this
    /// and proceeds only if it succeeds -- gating a Solana action on a dregg-proven
    /// fact with no trusted relayer.
    AssertProvenRoot { root: [u8; 32] },
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
                let mut lanes = [0u32; NUM_PUBLIC_INPUTS];
                for slot in lanes.iter_mut() {
                    *slot = u32::from_be_bytes(take::<4>(rest, &mut off));
                }
                Ok(Self::Settle {
                    a,
                    b,
                    c,
                    commitment,
                    commitment_pok,
                    lanes,
                })
            }
            TAG_ASSERT_PROVEN_ROOT => {
                if rest.len() != 32 {
                    return Err(SettlementError::InvalidInstruction);
                }
                let mut root = [0u8; 32];
                root.copy_from_slice(rest);
                Ok(Self::AssertProvenRoot { root })
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
                lanes,
            } => {
                let mut d = Vec::with_capacity(1 + SETTLE_LEN);
                d.push(TAG_SETTLE);
                d.extend_from_slice(a);
                d.extend_from_slice(b);
                d.extend_from_slice(c);
                d.extend_from_slice(commitment);
                d.extend_from_slice(commitment_pok);
                for l in lanes {
                    d.extend_from_slice(&l.to_be_bytes());
                }
                d
            }
            Self::AssertProvenRoot { root } => {
                let mut d = Vec::with_capacity(1 + 32);
                d.push(TAG_ASSERT_PROVEN_ROOT);
                d.extend_from_slice(root);
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
            lanes: [0x0777_7777u32; NUM_PUBLIC_INPUTS],
        };
        assert_eq!(SettlementInstruction::unpack(&i.pack()).unwrap(), i);
        assert_eq!(i.pack().len(), 1 + SETTLE_LEN);
        assert_eq!(SETTLE_LEN, 484, "384 B of proof + 25 * 4 B of lanes");
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

    /// ⚑ The OLD wire shape (25 * 32-byte scalars, `SETTLE_LEN` 1184) must REFUSE
    /// to load, not be reinterpreted. Per CLAUDE.md a broken format has to break
    /// loudly: the length check is exact, so a client still packing 32-byte scalars
    /// gets `InvalidInstruction` rather than a settle over garbage lanes.
    #[test]
    fn refuses_the_pre_2026_07_28_thirty_two_byte_lane_encoding() {
        let mut d = vec![TAG_SETTLE];
        d.extend_from_slice(&[1u8; 64 + 128 + 64 + 64 + 64]);
        for _ in 0..NUM_PUBLIC_INPUTS {
            let mut scalar = [0u8; 32];
            scalar[28..].copy_from_slice(&7u32.to_be_bytes());
            d.extend_from_slice(&scalar);
        }
        assert_eq!(d.len(), 1 + 384 + NUM_PUBLIC_INPUTS * 32);
        assert_eq!(d.len(), 1185, "the old settle payload was 1184 bytes");
        assert_eq!(
            SettlementInstruction::unpack(&d),
            Err(SettlementError::InvalidInstruction),
            "the superseded 32-byte-scalar lane encoding must refuse to load"
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
