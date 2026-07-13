//! The per-escrow record — the Solana twin of `DreggVault`'s `Escrow` struct
//! (`chain/contracts/DreggVault.sol`), the state machine that makes locking into a
//! DrEX trade SAFE.
//!
//! A locked escrow reaches EXACTLY ONE terminal state:
//!   • [`EscrowStatus::Released`] — paid to the ring-matched recipient, authorized
//!     by an M-of-N ed25519 oracle attestation over the canonical unlock message
//!     hash (the Solana AssertProvenRoot analog: the same threshold-attested
//!     clearing signal the [`crate::instruction::LockInstruction::Unlock`] pooled
//!     redeem uses), XOR
//!   • [`EscrowStatus::Refunded`] — reclaimed by the depositor once the per-escrow
//!     `deadline` has passed (the timeout IS the condition — no attestation needed).
//!
//! The two branches are mutually exclusive on `status`: release and refund each
//! require `Locked` and flip it to a terminal value BEFORE moving funds, so a
//! released escrow can never be refunded and vice-versa, and — because refund is
//! always reachable after the deadline with no external dependency — a lock is
//! never stuck.
//!
//! ## Custody disjointness
//!
//! Each escrow's SPL tokens live in their OWN per-escrow vault token account
//! (`[b"escrow_vault", config, escrow_id]`, authority `[b"escrow_authority",
//! config]`), DISJOINT from the pooled mirror vault (`config.vault_token_account`)
//! that [`crate::instruction::LockInstruction::Lock`]/`Unlock` use. So the pooled
//! redeem can never drain an escrow, and an escrow release/refund can never draw on
//! the pool — the exact analog of the EVM vault's `escrowedBalances` ⟂
//! `tokenBalances` split.

use crate::error::LockError;

/// Schema tag distinguishing an escrow record from a config account or foreign data.
pub const ESCROW_MAGIC: u8 = 0xE5;

/// Escrow record schema version.
pub const ESCROW_VERSION: u8 = 1;

/// The escrow state machine. `Locked` is the only non-terminal state; a release or
/// refund moves it to exactly one terminal value. A raw `0` byte is `None` (an
/// uninitialized / foreign account), never a valid live escrow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum EscrowStatus {
    /// No escrow (default for an all-zero account) — never a live state.
    None = 0,
    /// Funds held, not yet assignable.
    Locked = 1,
    /// Terminal: paid to the ring-matched recipient (attestation).
    Released = 2,
    /// Terminal: reclaimed by the depositor (timeout).
    Refunded = 3,
}

impl EscrowStatus {
    fn from_u8(b: u8) -> Result<Self, LockError> {
        match b {
            0 => Ok(Self::None),
            1 => Ok(Self::Locked),
            2 => Ok(Self::Released),
            3 => Ok(Self::Refunded),
            _ => Err(LockError::AccountState),
        }
    }
}

/// Fixed serialized size of [`EscrowRecord`]:
///   magic(1) ‖ version(1) ‖ status(1) ‖ mint(32) ‖ depositor(32)
///   ‖ refund_destination(32) ‖ amount_le(8) ‖ deadline_le(8, i64) ‖ escrow_id(32)
pub const ESCROW_RECORD_LEN: usize = 1 + 1 + 1 + 32 + 32 + 32 + 8 + 8 + 32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EscrowRecord {
    pub status: EscrowStatus,
    /// The SPL mint escrowed (== `config.mint`).
    pub mint: [u8; 32],
    /// The authority that locked; the only key allowed to refund.
    pub depositor: [u8; 32],
    /// The SPL token account a refund returns the tokens to (captured at lock).
    pub refund_destination: [u8; 32],
    /// The exact escrowed amount — the only amount a release/refund moves.
    pub amount: u64,
    /// Unix seconds; refund becomes available once `Clock.unix_timestamp > deadline`.
    pub deadline: i64,
    /// The escrow id (also the record PDA seed) — a globally unique per-lock nonce.
    pub escrow_id: [u8; 32],
}

impl EscrowRecord {
    pub fn pack_into(&self, dst: &mut [u8]) -> Result<(), LockError> {
        if dst.len() != ESCROW_RECORD_LEN {
            return Err(LockError::AccountState);
        }
        dst[0] = ESCROW_MAGIC;
        dst[1] = ESCROW_VERSION;
        dst[2] = self.status as u8;
        dst[3..35].copy_from_slice(&self.mint);
        dst[35..67].copy_from_slice(&self.depositor);
        dst[67..99].copy_from_slice(&self.refund_destination);
        dst[99..107].copy_from_slice(&self.amount.to_le_bytes());
        dst[107..115].copy_from_slice(&self.deadline.to_le_bytes());
        dst[115..147].copy_from_slice(&self.escrow_id);
        Ok(())
    }

    pub fn unpack(src: &[u8]) -> Result<Self, LockError> {
        if src.len() != ESCROW_RECORD_LEN {
            return Err(LockError::AccountState);
        }
        if src[0] != ESCROW_MAGIC || src[1] != ESCROW_VERSION {
            return Err(LockError::AccountState);
        }
        let status = EscrowStatus::from_u8(src[2])?;
        let mut mint = [0u8; 32];
        mint.copy_from_slice(&src[3..35]);
        let mut depositor = [0u8; 32];
        depositor.copy_from_slice(&src[35..67]);
        let mut refund_destination = [0u8; 32];
        refund_destination.copy_from_slice(&src[67..99]);
        let mut amt = [0u8; 8];
        amt.copy_from_slice(&src[99..107]);
        let mut dl = [0u8; 8];
        dl.copy_from_slice(&src[107..115]);
        let mut escrow_id = [0u8; 32];
        escrow_id.copy_from_slice(&src[115..147]);
        Ok(Self {
            status,
            mint,
            depositor,
            refund_destination,
            amount: u64::from_le_bytes(amt),
            deadline: i64::from_le_bytes(dl),
            escrow_id,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> EscrowRecord {
        EscrowRecord {
            status: EscrowStatus::Locked,
            mint: [1u8; 32],
            depositor: [2u8; 32],
            refund_destination: [3u8; 32],
            amount: 0x0102_0304_0506_0708,
            deadline: 1_700_000_000,
            escrow_id: [4u8; 32],
        }
    }

    #[test]
    fn record_roundtrip() {
        let r = sample();
        let mut buf = [0u8; ESCROW_RECORD_LEN];
        r.pack_into(&mut buf).unwrap();
        assert_eq!(buf[0], ESCROW_MAGIC);
        assert_eq!(buf[1], ESCROW_VERSION);
        assert_eq!(buf[2], EscrowStatus::Locked as u8);
        assert_eq!(EscrowRecord::unpack(&buf).unwrap(), r);
    }

    #[test]
    fn amount_and_deadline_are_little_endian() {
        let r = sample();
        let mut buf = [0u8; ESCROW_RECORD_LEN];
        r.pack_into(&mut buf).unwrap();
        assert_eq!(&buf[99..107], &r.amount.to_le_bytes());
        assert_eq!(&buf[107..115], &r.deadline.to_le_bytes());
    }

    #[test]
    fn unpack_rejects_all_zero() {
        // An all-zero account (magic 0) is not a valid escrow.
        assert_eq!(
            EscrowRecord::unpack(&[0u8; ESCROW_RECORD_LEN]),
            Err(LockError::AccountState)
        );
    }

    #[test]
    fn unpack_rejects_bad_status() {
        let r = sample();
        let mut buf = [0u8; ESCROW_RECORD_LEN];
        r.pack_into(&mut buf).unwrap();
        buf[2] = 9; // not a valid status
        assert_eq!(EscrowRecord::unpack(&buf), Err(LockError::AccountState));
    }

    #[test]
    fn unpack_rejects_wrong_len() {
        assert_eq!(
            EscrowRecord::unpack(&[ESCROW_MAGIC; ESCROW_RECORD_LEN - 1]),
            Err(LockError::AccountState)
        );
    }
}
