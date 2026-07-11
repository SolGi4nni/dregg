//! Fail-closed error set. Every rejection path in the processor maps to one of
//! these; `From<LockError> for ProgramError` lets `?` bubble to the runtime.

use solana_program::program_error::ProgramError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LockError {
    /// Bad tag, short/oversized instruction payload.
    InvalidInstruction = 0,
    /// A PDA account did not match its expected program-derived address.
    InvalidPda = 1,
    /// An account the program must own is owned by someone else, or the config /
    /// record is the wrong size.
    WrongOwner = 2,
    /// The passed mint / vault token account does not match the configured one.
    MintMismatch = 3,
    /// Amount is zero (dust / no-op lock or unlock rejected).
    ZeroAmount = 4,
    /// The unlock signer is not the configured unlock authority, or is not a signer.
    Unauthorized = 5,
    /// A required signer did not sign.
    MissingSigner = 6,
    /// Replay: the redeem-receipt PDA for this `redeem_id` already exists.
    AlreadyRedeemed = 7,
    /// The config / vault is already initialized, or not yet initialized.
    AccountState = 8,
    /// An account was not the expected one (wrong key passed in a fixed slot).
    AccountMismatch = 9,
}

impl From<LockError> for ProgramError {
    fn from(e: LockError) -> Self {
        ProgramError::Custom(e as u32)
    }
}
