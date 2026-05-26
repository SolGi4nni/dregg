// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./IDreggCredentialGate.sol";

/// @title DreggCredentialGate
/// @notice Verifies dregg anonymous credentials on-chain and gates actions (NFT mints, votes).
///
/// Uses SP1-wrapped STARK proofs to verify ring membership and predicate satisfaction
/// without learning the presenter's identity. Supports sybil resistance via per-action
/// nullifiers derived deterministically from the credential serial and action domain.
///
/// Implements a minimal ERC-721-like token for credential-gated mints, and a simple
/// governance voting mechanism for credential-gated governance.
contract DreggCredentialGate is IDreggCredentialGate {
    // ─── Immutables ─────────────────────────────────────────────────────────

    /// Address of the SP1 Verifier Gateway contract.
    address public immutable sp1Verifier;

    /// Verification key identifying the dregg credential verifier guest program.
    bytes32 public immutable programVkey;

    // ─── State ──────────────────────────────────────────────────────────────

    /// Spent presentation nullifiers (sybil resistance).
    mapping(bytes32 => bool) public usedNullifiers;

    /// Trusted federation roots. Only credentials proven against these roots are accepted.
    mapping(bytes32 => bool) public trustedFederations;

    /// Admin address (can add/remove trusted federations).
    address public admin;

    // ─── ERC-721-like State (minimal, non-standard) ─────────────────────────

    /// Next token ID to mint.
    uint256 public nextTokenId;

    /// Token ownership (tokenId -> owner).
    mapping(uint256 => address) public tokenOwner;

    /// Balance per address.
    mapping(address => uint256) public balanceOf;

    /// Token URI (tokenId -> uri).
    mapping(uint256 => string) public tokenURI;

    // ─── Governance State ───────────────────────────────────────────────────

    /// Votes per proposal (proposalId -> (yesVotes, noVotes)).
    mapping(uint256 => uint256) public yesVotes;
    mapping(uint256 => uint256) public noVotes;

    /// Per-proposal nullifier tracking (proposalId -> nullifier -> used).
    mapping(uint256 => mapping(bytes32 => bool)) public voteNullifiers;

    // ─── Events ─────────────────────────────────────────────────────────────

    /// Emitted when an NFT is minted via credential verification.
    event CredentialMint(
        uint256 indexed tokenId,
        address indexed recipient,
        bytes32 federationRoot,
        bytes32 predicateHash
    );

    /// Emitted when a vote is cast via credential verification.
    event CredentialVote(
        uint256 indexed proposalId,
        bool support,
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes32 nullifier
    );

    /// Emitted when a federation root is added/removed from the trusted set.
    event FederationTrustUpdated(bytes32 indexed federationRoot, bool trusted);

    // ─── Errors ─────────────────────────────────────────────────────────────

    error Unauthorized();
    error UntrustedFederation(bytes32 federationRoot);
    error ProofVerificationFailed();
    error NullifierAlreadyUsed(bytes32 nullifier);
    error TokenAlreadyMinted(uint256 tokenId);
    error AlreadyVoted(uint256 proposalId, bytes32 nullifier);
    error InvalidProofOutputs();

    // ─── Constructor ────────────────────────────────────────────────────────

    /// @param _sp1Verifier Address of the SP1 Verifier Gateway.
    /// @param _programVkey Verification key for the dregg credential verifier program.
    /// @param _admin Admin address for managing trusted federations.
    constructor(address _sp1Verifier, bytes32 _programVkey, address _admin) {
        sp1Verifier = _sp1Verifier;
        programVkey = _programVkey;
        admin = _admin;
    }

    // ─── Admin ──────────────────────────────────────────────────────────────

    /// Add or remove a federation root from the trusted set.
    function setFederationTrust(bytes32 federationRoot, bool trusted) external {
        if (msg.sender != admin) revert Unauthorized();
        trustedFederations[federationRoot] = trusted;
        emit FederationTrustUpdated(federationRoot, trusted);
    }

    // ─── Credential Verification ────────────────────────────────────────────

    /// @inheritdoc IDreggCredentialGate
    function verifyCredential(
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external view returns (bool) {
        // Check federation is trusted.
        if (!trustedFederations[federationRoot]) revert UntrustedFederation(federationRoot);

        // Decode and verify the SP1 proof.
        (bytes memory proofBytes, bytes memory publicValues) = abi.decode(
            sp1Proof,
            (bytes, bytes)
        );

        // Call the SP1 Verifier Gateway (staticcall since this is view).
        (bool verifySuccess, ) = sp1Verifier.staticcall(
            abi.encodeWithSignature(
                "verifyProof(bytes32,bytes,bytes)",
                programVkey,
                publicValues,
                proofBytes
            )
        );
        if (!verifySuccess) return false;

        // Decode public values: (bool valid, bytes32 federationRoot, bytes32 predicateHash, bytes32 nullifier)
        (
            bool valid,
            bytes32 proofFedRoot,
            bytes32 proofPredHash,
            /* bytes32 nullifier -- not checked in view function */
        ) = abi.decode(publicValues, (bool, bytes32, bytes32, bytes32));

        // Ensure the proof matches the claimed parameters.
        if (!valid) return false;
        if (proofFedRoot != federationRoot) return false;
        if (proofPredHash != predicateHash) return false;

        return true;
    }

    /// @inheritdoc IDreggCredentialGate
    function mintWithCredential(
        uint256 tokenId,
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external {
        // Check federation is trusted.
        if (!trustedFederations[federationRoot]) revert UntrustedFederation(federationRoot);

        // Check token not already minted.
        if (tokenOwner[tokenId] != address(0)) revert TokenAlreadyMinted(tokenId);

        // Decode and verify the SP1 proof.
        (bytes memory proofBytes, bytes memory publicValues) = abi.decode(
            sp1Proof,
            (bytes, bytes)
        );

        (bool verifySuccess, ) = sp1Verifier.staticcall(
            abi.encodeWithSignature(
                "verifyProof(bytes32,bytes,bytes)",
                programVkey,
                publicValues,
                proofBytes
            )
        );
        if (!verifySuccess) revert ProofVerificationFailed();

        // Decode public values.
        (
            bool valid,
            bytes32 proofFedRoot,
            bytes32 proofPredHash,
            bytes32 nullifier
        ) = abi.decode(publicValues, (bool, bytes32, bytes32, bytes32));

        if (!valid) revert ProofVerificationFailed();
        if (proofFedRoot != federationRoot) revert InvalidProofOutputs();
        if (proofPredHash != predicateHash) revert InvalidProofOutputs();

        // Sybil resistance: check nullifier not already used for minting.
        if (usedNullifiers[nullifier]) revert NullifierAlreadyUsed(nullifier);
        usedNullifiers[nullifier] = true;

        // Mint the token to msg.sender.
        tokenOwner[tokenId] = msg.sender;
        balanceOf[msg.sender] += 1;
        if (nextTokenId <= tokenId) {
            nextTokenId = tokenId + 1;
        }

        emit CredentialVerified(federationRoot, predicateHash, nullifier);
        emit CredentialMint(tokenId, msg.sender, federationRoot, predicateHash);
    }

    /// @inheritdoc IDreggCredentialGate
    function voteWithCredential(
        uint256 proposalId,
        bool support,
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof
    ) external {
        // Check federation is trusted.
        if (!trustedFederations[federationRoot]) revert UntrustedFederation(federationRoot);

        // Decode and verify the SP1 proof.
        (bytes memory proofBytes, bytes memory publicValues) = abi.decode(
            sp1Proof,
            (bytes, bytes)
        );

        (bool verifySuccess, ) = sp1Verifier.staticcall(
            abi.encodeWithSignature(
                "verifyProof(bytes32,bytes,bytes)",
                programVkey,
                publicValues,
                proofBytes
            )
        );
        if (!verifySuccess) revert ProofVerificationFailed();

        // Decode public values.
        (
            bool valid,
            bytes32 proofFedRoot,
            bytes32 proofPredHash,
            bytes32 nullifier
        ) = abi.decode(publicValues, (bool, bytes32, bytes32, bytes32));

        if (!valid) revert ProofVerificationFailed();
        if (proofFedRoot != federationRoot) revert InvalidProofOutputs();
        if (proofPredHash != predicateHash) revert InvalidProofOutputs();

        // Per-proposal sybil resistance: each credential can only vote once per proposal.
        if (voteNullifiers[proposalId][nullifier]) revert AlreadyVoted(proposalId, nullifier);
        voteNullifiers[proposalId][nullifier] = true;

        // Record the vote.
        if (support) {
            yesVotes[proposalId] += 1;
        } else {
            noVotes[proposalId] += 1;
        }

        emit CredentialVerified(federationRoot, predicateHash, nullifier);
        emit CredentialVote(proposalId, support, federationRoot, predicateHash, nullifier);
    }

    // ─── View Functions ─────────────────────────────────────────────────────

    /// @inheritdoc IDreggCredentialGate
    function isNullifierUsed(bytes32 nullifier) external view returns (bool) {
        return usedNullifiers[nullifier];
    }

    /// Get the vote count for a proposal.
    function getVotes(uint256 proposalId) external view returns (uint256 yes, uint256 no) {
        return (yesVotes[proposalId], noVotes[proposalId]);
    }
}
