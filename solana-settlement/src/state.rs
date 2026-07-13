//! The program-owned settlement state account -- the Solana twin of the EVM
//! `DreggSettlement` storage (`_provenLanes`, `_provenHeight`, `_genesisLanes`,
//! `_verifyingKeyHash`).
//!
//! ## Fail-closed / NOMAD-LAW
//!
//! [`SettlementState::unpack`] REJECTS any account whose magic/version/size is
//! wrong, so an uninitialized (all-zero) or foreign account can never be read as
//! valid state. [`SettlementState::pack_into`] refuses to write a state with a
//! non-canonical lane or a zero VK hash.

use crate::error::SettlementError;

/// BabyBear prime p = 2^31 - 2^27 + 1. Every settlement lane must be `< p`
/// (the EVM `BABYBEAR_P`).
pub const BABYBEAR_P: u32 = 2013265921;

/// One-byte schema tag so an uninitialized/foreign account is not mistaken for
/// valid settlement state.
pub const STATE_MAGIC: u8 = 0xD5;

/// Schema version.
pub const STATE_VERSION: u8 = 1;

/// Serialized size:
///   magic(1) || version(1) || proven_height(8) || proven_root(32)
///   || genesis_root(32) || vk_hash(32) = 106
pub const STATE_LEN: usize = 1 + 1 + 8 + 32 + 32 + 32;

/// Is `v` a canonical BabyBear residue (`< p`)?
pub fn is_canonical_lane(v: u32) -> bool {
    v < BABYBEAR_P
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettlementState {
    /// Cumulative proven height (finalized turns; strictly monotone).
    pub proven_height: u64,
    /// The current proven dregg state root, as 8 BabyBear lanes.
    pub proven_root: [u32; 8],
    /// The genesis anchor pinned at init (the first proof's `genesis_root`).
    pub genesis_root: [u32; 8],
    /// keccak256 of the pinned Groth16 verifying key -- the on-chain commitment to
    /// `EthSettlementProof.verifying_key_hash`, byte-identical to the live EVM pin.
    pub vk_hash: [u8; 32],
}

fn write_lanes(dst: &mut [u8], lanes: &[u32; 8]) {
    for (i, l) in lanes.iter().enumerate() {
        dst[i * 4..i * 4 + 4].copy_from_slice(&l.to_be_bytes());
    }
}

fn read_lanes(src: &[u8]) -> [u32; 8] {
    let mut lanes = [0u32; 8];
    for (i, l) in lanes.iter_mut().enumerate() {
        let mut b = [0u8; 4];
        b.copy_from_slice(&src[i * 4..i * 4 + 4]);
        *l = u32::from_be_bytes(b);
    }
    lanes
}

impl SettlementState {
    pub fn pack_into(&self, dst: &mut [u8]) -> Result<(), SettlementError> {
        if dst.len() != STATE_LEN {
            return Err(SettlementError::AccountState);
        }
        // Never serialize a state with a non-canonical lane or a zero VK hash.
        for l in self.proven_root.iter().chain(self.genesis_root.iter()) {
            if !is_canonical_lane(*l) {
                return Err(SettlementError::NonCanonicalLane);
            }
        }
        if self.vk_hash == [0u8; 32] {
            return Err(SettlementError::InvalidGenesis);
        }
        dst[0] = STATE_MAGIC;
        dst[1] = STATE_VERSION;
        dst[2..10].copy_from_slice(&self.proven_height.to_le_bytes());
        write_lanes(&mut dst[10..42], &self.proven_root);
        write_lanes(&mut dst[42..74], &self.genesis_root);
        dst[74..106].copy_from_slice(&self.vk_hash);
        Ok(())
    }

    pub fn unpack(src: &[u8]) -> Result<Self, SettlementError> {
        if src.len() != STATE_LEN {
            return Err(SettlementError::AccountState);
        }
        if src[0] != STATE_MAGIC || src[1] != STATE_VERSION {
            return Err(SettlementError::AccountState);
        }
        let mut h = [0u8; 8];
        h.copy_from_slice(&src[2..10]);
        let proven_root = read_lanes(&src[10..42]);
        let genesis_root = read_lanes(&src[42..74]);
        let mut vk_hash = [0u8; 32];
        vk_hash.copy_from_slice(&src[74..106]);
        Ok(Self {
            proven_height: u64::from_le_bytes(h),
            proven_root,
            genesis_root,
            vk_hash,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let s = SettlementState {
            proven_height: 2,
            proven_root: [1, 2, 3, 4, 5, 6, 7, 8],
            genesis_root: [9, 10, 11, 12, 13, 14, 15, 16],
            vk_hash: [0x11; 32],
        };
        let mut buf = [0u8; STATE_LEN];
        s.pack_into(&mut buf).unwrap();
        assert_eq!(buf[0], STATE_MAGIC);
        assert_eq!(SettlementState::unpack(&buf).unwrap(), s);
    }

    #[test]
    fn unpack_rejects_zero_account() {
        assert_eq!(
            SettlementState::unpack(&[0u8; STATE_LEN]),
            Err(SettlementError::AccountState)
        );
    }

    #[test]
    fn pack_rejects_non_canonical_lane() {
        let s = SettlementState {
            proven_height: 0,
            proven_root: [BABYBEAR_P, 0, 0, 0, 0, 0, 0, 0],
            genesis_root: [0; 8],
            vk_hash: [0x11; 32],
        };
        let mut buf = [0u8; STATE_LEN];
        assert_eq!(
            s.pack_into(&mut buf),
            Err(SettlementError::NonCanonicalLane)
        );
    }

    #[test]
    fn pack_rejects_zero_vk_hash() {
        let s = SettlementState {
            proven_height: 0,
            proven_root: [1; 8],
            genesis_root: [1; 8],
            vk_hash: [0u8; 32],
        };
        let mut buf = [0u8; STATE_LEN];
        assert_eq!(s.pack_into(&mut buf), Err(SettlementError::InvalidGenesis));
    }
}
