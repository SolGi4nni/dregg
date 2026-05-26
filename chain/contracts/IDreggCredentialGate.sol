// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IDreggCredentialGate
/// @notice Verifies dregg anonymous credentials on-chain without learning the presenter's identity.
///
/// This contract enables smart contracts on Base to gate actions behind anonymous credential
/// verification. A user proves they hold a valid credential from a specific federation
/// (e.g., "verified adult", "KYC'd user", "token holder") WITHOUT revealing:
///   - Their identity (which federation member they are)
///   - Their credential's serial number
///   - Any attributes beyond the proven predicate
///   - Whether they've used this gate before (unlinkable presentations)
///
/// The verification flow:
///   1. User generates an anonymous presentation (ring membership + predicate proof)
///   2. The presentation STARK is wrapped in SP1 -> Groth16
///   3. User submits the Groth16 proof to this contract
///   4. Contract verifies via SP1 Verifier Gateway
///   5. If valid, the gated action executes
///
/// The SP1 guest program verifies:
///   - Ring membership: user's key is in the federation's member tree (which member = hidden)
///   - Predicate satisfaction: a private attribute satisfies a public condition
///   - Credential binding: the proof is bound to a validly-issued credential
interface IDreggCredentialGate {
    /// @notice Emitted when an anonymous credential is successfully verified.
    /// @param federationRoot The federation whose membership tree was proven against.
    /// @param predicateHash The predicate that was proven (e.g., keccak256("age >= 18")).
    /// @param presentationNullifier A per-action nullifier for sybil resistance (optional).
    event CredentialVerified(
        bytes32 indexed federationRoot,
        bytes32 indexed predicateHash,
        bytes32 presentationNullifier
    );

    /// @notice Verify a dregg anonymous credential without learning the presenter's identity.
    /// @dev This is a view function -- it does not modify state. Use it for read-only checks
    ///      or compose it with state-modifying functions that gate on the result.
    ///
    ///      The sp1Proof encodes:
    ///        - Groth16 proof bytes
    ///        - Public values: (federationRoot, predicateHash, valid=true)
    ///        - Program vkey identifying the dregg credential verifier program
    ///
    /// @param federationRoot The root of the federation member tree (identifies issuing federation).
    /// @param predicateHash What is being proven (e.g., keccak256("age >= 18")).
    /// @param sp1Proof The SP1-wrapped Groth16 proof of the anonymous credential presentation.
    /// @return True if the credential is valid.
    function verifyCredential(
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external view returns (bool);

    /// @notice Gate an NFT mint behind anonymous credential verification.
    /// @dev Verifies the credential, then mints the NFT. The minter's identity remains hidden --
    ///      only the fact that they hold a valid credential is proven.
    ///
    ///      Sybil resistance: uses a presentation nullifier derived deterministically from
    ///      (credential_serial, action_domain="mint", tokenId). Each credential can only mint
    ///      each tokenId once, but the nullifier is unlinkable to the credential's identity.
    ///
    /// @param tokenId The NFT token ID to mint.
    /// @param federationRoot The federation root (which federation issued the credential).
    /// @param predicateHash The predicate being proven.
    /// @param sp1Proof The SP1-wrapped Groth16 proof.
    function mintWithCredential(
        uint256 tokenId,
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external;

    /// @notice Gate a vote behind anonymous credential verification.
    /// @dev Verifies the credential proves sufficient token holdings, then records the vote.
    ///      Uses a vote-specific nullifier to prevent double-voting while preserving anonymity.
    ///
    /// @param proposalId The governance proposal being voted on.
    /// @param support True for yes, false for no.
    /// @param federationRoot The federation root.
    /// @param predicateHash The predicate (e.g., keccak256("balance >= 1000")).
    /// @param sp1Proof The SP1-wrapped Groth16 proof.
    function voteWithCredential(
        uint256 proposalId,
        bool support,
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external;

    /// @notice Check if a presentation nullifier has been used for a specific action.
    /// @param nullifier The presentation nullifier.
    /// @return True if already used.
    function isNullifierUsed(bytes32 nullifier) external view returns (bool);
}
