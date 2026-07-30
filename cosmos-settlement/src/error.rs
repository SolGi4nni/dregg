use cosmwasm_std::StdError;
use thiserror::Error;

use crate::verifier::VerifyError;

/// Settlement contract errors — the Cosmos twin of the custom errors in
/// `IDreggSettlement.sol` (`ProofRejected`, `ContinuityBroken`, `ZeroTurns`,
/// `NonCanonicalLane`, `VerifyingKeyHashMismatch`).
#[derive(Error, Debug, PartialEq)]
pub enum ContractError {
    #[error(transparent)]
    Std(#[from] StdError),

    /// A lane is not a canonical BabyBear element (>= p = 2^31 - 2^27 + 1).
    #[error("non-canonical BabyBear lane at index {index}: {value}")]
    NonCanonicalLane { index: usize, value: u32 },

    /// A settlement must advance at least one turn.
    #[error("zero turns: a settlement must advance the chain")]
    ZeroTurns,

    /// The proof's genesis lanes do not equal the current proven root.
    #[error("continuity broken: proof genesis root != current proven root")]
    ContinuityBroken,

    /// The verifying-key digest declared at instantiation is not the digest of
    /// the key this contract verifies against (`vk::VK_DIGEST`).
    ///
    /// ⚑ Replaced `ZeroVerifyingKeyHash` on 2026-07-30. That check was
    /// `msg.verifying_key_hash.trim_start_matches("0x").trim_matches('0')
    /// .is_empty()` — it refused only all-zero strings and accepted every other
    /// value, including `"0x1"` and the superseded label hash. Nothing compared
    /// the pin afterwards either: `settle` never read it, so the "commitment"
    /// committed to whatever the instantiator typed. The EVM
    /// `VerifyingKeyHashMismatch` and Solana `VkDigestMismatch` twin.
    #[error("verifying-key digest mismatch: expected {expected}, got {given}")]
    VkDigestMismatch { expected: String, given: String },

    /// The declared verifying-key digest is not 32 bytes of hex (with or
    /// without a `0x` prefix), so it cannot denote a key at all.
    #[error("malformed verifying-key digest: {0}")]
    MalformedVkDigest(String),

    /// The Groth16 proof (or its Pedersen commitment) failed to verify.
    #[error("proof rejected: {0}")]
    ProofRejected(String),
}

impl From<VerifyError> for ContractError {
    fn from(e: VerifyError) -> Self {
        ContractError::ProofRejected(e.to_string())
    }
}
