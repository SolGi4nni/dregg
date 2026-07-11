//! The program-owned config account schema (the vault's on-chain state).
//!
//! This is the program's OWN account schema (not the relayer-facing one — that is
//! the 72-byte lock record in [`crate::record`]). It records the mint being
//! mirrored, the unlock authority, the SPL token vault account, the vault-authority
//! PDA bump, and the monotonic lock nonce that makes each `lock_id` unique.

use crate::error::LockError;

/// A one-byte schema tag so an uninitialized (all-zero) or foreign account is not
/// mistaken for a valid config.
pub const CONFIG_MAGIC: u8 = 0xD9;

/// Fixed serialized size of [`VaultConfig`].
///   magic(1) ‖ mint(32) ‖ unlock_authority(32) ‖ vault_token_account(32)
///   ‖ vault_authority_bump(1) ‖ nonce_le(8)  = 106
pub const CONFIG_LEN: usize = 1 + 32 + 32 + 32 + 1 + 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VaultConfig {
    /// The $DREGG SPL mint this vault mirrors.
    pub mint: [u8; 32],
    /// The ed25519 pubkey allowed to authorize [`crate::instruction::LockInstruction::Unlock`].
    pub unlock_authority: [u8; 32],
    /// The SPL token account custodying locked $DREGG (SPL authority = vault-authority PDA).
    pub vault_token_account: [u8; 32],
    /// Bump of the vault-authority PDA (seeds `[b"vault_authority", config]`).
    pub vault_authority_bump: u8,
    /// Monotonic counter; the next lock consumes this value then increments it.
    /// Feeds the per-lock record PDA seed, making each `lock_id` unique.
    pub nonce: u64,
}

impl VaultConfig {
    pub fn pack_into(&self, dst: &mut [u8]) -> Result<(), LockError> {
        if dst.len() != CONFIG_LEN {
            return Err(LockError::AccountState);
        }
        dst[0] = CONFIG_MAGIC;
        dst[1..33].copy_from_slice(&self.mint);
        dst[33..65].copy_from_slice(&self.unlock_authority);
        dst[65..97].copy_from_slice(&self.vault_token_account);
        dst[97] = self.vault_authority_bump;
        dst[98..106].copy_from_slice(&self.nonce.to_le_bytes());
        Ok(())
    }

    pub fn unpack(src: &[u8]) -> Result<Self, LockError> {
        if src.len() != CONFIG_LEN {
            return Err(LockError::AccountState);
        }
        if src[0] != CONFIG_MAGIC {
            return Err(LockError::AccountState);
        }
        let mut mint = [0u8; 32];
        mint.copy_from_slice(&src[1..33]);
        let mut unlock_authority = [0u8; 32];
        unlock_authority.copy_from_slice(&src[33..65]);
        let mut vault_token_account = [0u8; 32];
        vault_token_account.copy_from_slice(&src[65..97]);
        let vault_authority_bump = src[97];
        let mut n = [0u8; 8];
        n.copy_from_slice(&src[98..106]);
        Ok(Self {
            mint,
            unlock_authority,
            vault_token_account,
            vault_authority_bump,
            nonce: u64::from_le_bytes(n),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn config_roundtrip() {
        let c = VaultConfig {
            mint: [1u8; 32],
            unlock_authority: [2u8; 32],
            vault_token_account: [3u8; 32],
            vault_authority_bump: 254,
            nonce: 0x0102_0304_0506_0708,
        };
        let mut buf = [0u8; CONFIG_LEN];
        c.pack_into(&mut buf).unwrap();
        assert_eq!(buf[0], CONFIG_MAGIC);
        assert_eq!(VaultConfig::unpack(&buf).unwrap(), c);
    }

    #[test]
    fn unpack_rejects_bad_magic() {
        let buf = [0u8; CONFIG_LEN]; // magic byte 0, not CONFIG_MAGIC
        assert_eq!(VaultConfig::unpack(&buf), Err(LockError::AccountState));
    }

    #[test]
    fn unpack_rejects_wrong_len() {
        assert_eq!(
            VaultConfig::unpack(&[CONFIG_MAGIC; CONFIG_LEN - 1]),
            Err(LockError::AccountState)
        );
    }
}
