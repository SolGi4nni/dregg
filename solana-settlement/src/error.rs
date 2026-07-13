//! Fail-closed error set for the dregg Solana settlement program. Every rejection
//! path maps to one of these; `From<SettlementError> for ProgramError` lets `?`
//! bubble to the runtime. These mirror the typed reverts of the EVM
//! `IDreggSettlement` (`ContinuityBroken`, `ZeroTurns`, `NonCanonicalLane`,
//! `ProofRejected`, ...).

use solana_program::program_error::ProgramError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SettlementError {
    /// Bad tag, or a short/oversized instruction payload.
    InvalidInstruction = 0,
    /// A state account the program must own is owned by someone else, is the wrong
    /// size, or carries the wrong magic/version.
    AccountState = 1,
    /// The settlement state account is already initialized (init) or not yet
    /// initialized (settle).
    AlreadyInitialized = 2,
    /// A lane is not a canonical BabyBear residue (`>= 2013265921`). Mirrors the
    /// EVM `NonCanonicalLane`.
    NonCanonicalLane = 3,
    /// `num_turns == 0`: height would not strictly advance. Mirrors EVM `ZeroTurns`.
    ZeroTurns = 4,
    /// The proof's genesis lanes do not chain from the current proven root.
    /// Mirrors EVM `ContinuityBroken`.
    ContinuityBroken = 5,
    /// The pinned genesis anchor is non-canonical, or the pinned VK hash is zero.
    InvalidGenesis = 6,
    /// The Groth16 verifier rejected the proof (commitment PoK or pairing failed).
    /// Mirrors EVM `ProofRejected` / `ProofInvalid`.
    ProofRejected = 7,
    /// A required signer did not sign (the payer on init).
    MissingSigner = 8,
}

impl From<SettlementError> for ProgramError {
    fn from(e: SettlementError) -> Self {
        ProgramError::Custom(e as u32)
    }
}
