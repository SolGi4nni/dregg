// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IPyanaVault
/// @notice Holds bridged assets (ERC-20 tokens and ETH) with private note-based accounting.
///
/// Users deposit tokens into the vault, receiving a note commitment in pyana's private
/// note tree. Inside pyana, transfers are fully private (sender/receiver/amount hidden).
/// To withdraw, the user burns their pyana note and presents an SP1-wrapped STARK proof
/// that verifies the note was valid and unspent.
///
/// The vault tracks nullifiers to prevent double-withdrawal. Each note can only be
/// withdrawn once, regardless of how many times the user transfers it inside pyana.
interface IPyanaVault {
    /// @notice Emitted when a user deposits tokens into the vault.
    /// @param token The ERC-20 token address (address(0) for native ETH).
    /// @param amount The amount deposited.
    /// @param noteCommitment The pyana note commitment (Poseidon2 hash of note contents).
    /// @param leafIndex The index in the note commitment tree where this note was inserted.
    event Deposit(
        address indexed token,
        uint256 amount,
        bytes32 noteCommitment,
        uint256 leafIndex
    );

    /// @notice Emitted when a user withdraws tokens from the vault via proof.
    /// @param token The ERC-20 token address (address(0) for native ETH).
    /// @param amount The amount withdrawn.
    /// @param recipient The address receiving the tokens.
    /// @param nullifier The note's nullifier (prevents double-spend).
    event Withdrawal(
        address indexed token,
        uint256 amount,
        address indexed recipient,
        bytes32 nullifier
    );

    /// @notice Deposit ERC-20 tokens into the vault, creating a private note.
    /// @dev The caller must have approved the vault to spend `amount` of `token`.
    ///      The note commitment is added to the on-chain Merkle tree and the
    ///      pyana federation observes the event to mirror the commitment.
    /// @param token The ERC-20 token address.
    /// @param amount The amount to deposit.
    /// @param noteCommitment The Poseidon2 commitment to the note (owner, value, asset, randomness).
    function deposit(address token, uint256 amount, bytes32 noteCommitment) external;

    /// @notice Deposit native ETH into the vault, creating a private note.
    /// @param noteCommitment The Poseidon2 commitment to the note.
    function depositETH(bytes32 noteCommitment) external payable;

    /// @notice Withdraw tokens from the vault by presenting a valid SP1 proof.
    /// @dev The SP1 proof wraps a STARK proof that verifies:
    ///      1. The note exists in the attested note tree (Merkle membership)
    ///      2. The nullifier is correctly derived from the note (ownership proof)
    ///      3. The withdrawal amount matches the note's value
    ///      4. The recipient address is bound into the proof (front-running prevention)
    ///
    ///      The proof is verified via the SP1 Verifier Gateway. If valid, the vault
    ///      releases the tokens and records the nullifier as spent.
    /// @param token The ERC-20 token address (address(0) for native ETH).
    /// @param amount The amount to withdraw.
    /// @param recipient The address to receive the tokens.
    /// @param sp1Proof The SP1-wrapped Groth16 proof (proof bytes + public values).
    function withdraw(
        address token,
        uint256 amount,
        address recipient,
        bytes calldata sp1Proof
    ) external;

    /// @notice Check if a nullifier has already been used (note already withdrawn).
    /// @param nullifier The nullifier to check.
    /// @return True if the nullifier has been used.
    function isNullifierUsed(bytes32 nullifier) external view returns (bool);

    /// @notice Get the current note tree root (for proof generation reference).
    /// @return The current Merkle root of all deposited note commitments.
    function noteTreeRoot() external view returns (bytes32);

    /// @notice Get the total number of deposits (and thus the next leaf index).
    /// @return The number of notes in the commitment tree.
    function depositCount() external view returns (uint256);
}
