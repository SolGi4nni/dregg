use cosmwasm_std::StdError;
use thiserror::Error;

use crate::verifier::VerifyError;

/// Settlement contract errors — the Cosmos twin of the custom errors in
/// `IDreggSettlement.sol` (`ProofRejected`, `ContinuityBroken`, `ZeroTurns`,
/// `NonCanonicalLane`, `ZeroVerifyingKeyHash`).
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

    /// The verifying-key hash pinned at instantiation must be non-zero.
    #[error("zero verifying-key hash")]
    ZeroVerifyingKeyHash,

    /// The Groth16 proof (or its Pedersen commitment) failed to verify.
    #[error("proof rejected: {0}")]
    ProofRejected(String),
}

impl From<VerifyError> for ContractError {
    fn from(e: VerifyError) -> Self {
        ContractError::ProofRejected(e.to_string())
    }
}
