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

    // ─── Action-binding domain tags (#13) ────────────────────────────────────
    //
    // The SP1 credential proof now ALSO binds the PRESENTER and the SPECIFIC
    // ACTION: the guest commits `(… , address boundSender, bytes32 boundAction)`,
    // and mint/vote check `boundSender == msg.sender` and `boundAction ==` the
    // action hash recomputed on-chain. Before this, the proof bound only
    // (valid, fedRoot, predHash, nullifier), so it could be sniped from the
    // mempool — a front-runner stole the mint, voted OPPOSITE (flip `support`),
    // or voted EVERY proposal (reuse across `proposalId`). The action hash folds
    // `address(this)` + `block.chainid` too, so a credential proof also cannot be
    // replayed on another gate deployment or chain.
    //
    // NOTE: the check only bites once the guest commits these values — the
    // companion circuit change (the SP1 credential-presentation statement) is
    // off-chain, not authored here.
    bytes32 public constant ACTION_MINT = keccak256("dregg.credential.mint.v1");
    bytes32 public constant ACTION_VOTE = keccak256("dregg.credential.vote.v1");

    // ─── State ──────────────────────────────────────────────────────────────

    /// Spent presentation nullifiers (sybil resistance). The key is the BARE
    /// nullifier the proof commits: one credential presentation = one mint, ever.
    ///
    /// Per-tokenId minting (the interface's aspirational (serial, domain, tokenId)
    /// scoping) is UNSOUND under the current proof format, which exposes only
    /// (valid, fedRoot, predHash, nullifier) — `tokenId` is a caller-supplied
    /// argument the proof never binds, so scoping the key by tokenId would let one
    /// credential replay-mint unlimited NFTs (tokenId = 0,1,2,…). Per-tokenId
    /// scoping is safe ONLY once tokenId (or an action domain that includes it) is
    /// folded into the presentation nullifier and exposed as a checked public value.
    mapping(bytes32 => bool) public usedNullifiers;

    /// Trusted federation roots. Only credentials proven against these roots are accepted.
    mapping(bytes32 => bool) public trustedFederations;

    /// Admin address (can add/remove trusted federations).
    address public admin;

    /// Proposed next admin (two-step rotation: proposeAdmin then acceptAdmin).
    address public pendingAdmin;

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

    /// Emitted when an admin rotation is proposed.
    event AdminProposed(address indexed currentAdmin, address indexed proposedAdmin);

    /// Emitted when a proposed admin accepts and the rotation completes.
    event AdminTransferred(address indexed previousAdmin, address indexed newAdmin);

    // ─── Errors ─────────────────────────────────────────────────────────────

    error Unauthorized();
    error UntrustedFederation(bytes32 federationRoot);
    error ProofVerificationFailed();
    error NullifierAlreadyUsed(bytes32 nullifier);
    error TokenAlreadyMinted(uint256 tokenId);
    error AlreadyVoted(uint256 proposalId, bytes32 nullifier);
    error InvalidProofOutputs();
    error VerifierNotContract();
    /// The proof is bound to a DIFFERENT presenter than `msg.sender` (#13 snipe).
    error SenderBindingMismatch(address boundSender, address caller);
    /// The proof is bound to a DIFFERENT action than the one being performed
    /// (wrong tokenId / proposalId / support, or wrong gate/chain) (#13 snipe).
    error ActionBindingMismatch(bytes32 boundAction, bytes32 expectedAction);

    // ─── Constructor ────────────────────────────────────────────────────────

    /// @param _sp1Verifier Address of the SP1 Verifier Gateway.
    /// @param _programVkey Verification key for the dregg credential verifier program.
    /// @param _admin Admin address for managing trusted federations.
    constructor(address _sp1Verifier, bytes32 _programVkey, address _admin) {
        // Fail-closed: a staticcall to a codeless address returns success, so a
        // misconfigured verifier would silently accept every proof. Refuse to
        // deploy against an address with no code.
        if (_sp1Verifier.code.length == 0) revert VerifierNotContract();
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

    /// @inheritdoc IDreggCredentialGate
    function proposeAdmin(address newAdmin) external {
        if (msg.sender != admin) revert Unauthorized();
        pendingAdmin = newAdmin;
        emit AdminProposed(admin, newAdmin);
    }

    /// @inheritdoc IDreggCredentialGate
    function acceptAdmin() external {
        if (msg.sender != pendingAdmin) revert Unauthorized();
        emit AdminTransferred(admin, msg.sender);
        admin = msg.sender;
        pendingAdmin = address(0);
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

        // Fail-closed: a staticcall to a codeless address succeeds vacuously,
        // so a verifier with no code must never be able to accept.
        if (sp1Verifier.code.length == 0) revert VerifierNotContract();

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

        // Verify + decode + bind: the proof must be valid, match (fedRoot,predHash),
        // be presented by THIS caller, and be bound to THIS exact mint (#13 — the
        // action hash pins tokenId, so a sniped proof cannot steal a different mint).
        bytes32 expectedAction = keccak256(abi.encode(address(this), block.chainid, ACTION_MINT, tokenId));
        bytes32 nullifier = _verifyBindDecode(federationRoot, predicateHash, sp1Proof, expectedAction);

        // Sybil resistance: the BARE presentation nullifier is the replay key —
        // one credential presentation mints exactly one token. tokenId is NOT bound
        // in the proof, so it must not scope the key (see `usedNullifiers`).
        if (usedNullifiers[nullifier]) revert NullifierAlreadyUsed(nullifier);
        usedNullifiers[nullifier] = true;

        // Check token not already minted.
        if (tokenOwner[tokenId] != address(0)) revert TokenAlreadyMinted(tokenId);

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

        // Verify + decode + bind: the proof must be valid, match (fedRoot,predHash),
        // be presented by THIS caller, and be bound to THIS exact vote (#13 — the
        // action hash pins proposalId AND support, so a sniped proof cannot vote for
        // a different proposal nor be flipped to the opposite side).
        bytes32 expectedAction =
            keccak256(abi.encode(address(this), block.chainid, ACTION_VOTE, proposalId, support));
        bytes32 nullifier = _verifyBindDecode(federationRoot, predicateHash, sp1Proof, expectedAction);

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

    // ─── Internal ───────────────────────────────────────────────────────────

    /// Fail-closed-verify the SP1 proof, decode its extended public values, and
    /// enforce ALL of: valid, matching (fedRoot, predHash), presenter == msg.sender,
    /// and `boundAction == expectedAction` (#13 presenter+action binding). Returns
    /// the presentation nullifier. Split out of mint/vote to keep them under the
    /// stack-depth limit. `view`: it only reads, and a private call preserves the
    /// caller's `msg.sender`.
    function _verifyBindDecode(
        bytes32 federationRoot,
        bytes32 predicateHash,
        bytes calldata sp1Proof,
        bytes32 expectedAction
    ) private view returns (bytes32 nullifier) {
        // Fail-closed verifier guard (see verifyCredential).
        if (sp1Verifier.code.length == 0) revert VerifierNotContract();

        (bytes memory proofBytes, bytes memory publicValues) = abi.decode(sp1Proof, (bytes, bytes));

        (bool verifySuccess, ) = sp1Verifier.staticcall(
            abi.encodeWithSignature(
                "verifyProof(bytes32,bytes,bytes)", programVkey, publicValues, proofBytes
            )
        );
        if (!verifySuccess) revert ProofVerificationFailed();

        // Public values now carry the presenter + action binding (#13):
        // (bool valid, bytes32 fedRoot, bytes32 predHash, bytes32 nullifier,
        //  address boundSender, bytes32 boundAction)
        (
            bool valid,
            bytes32 proofFedRoot,
            bytes32 proofPredHash,
            bytes32 nf,
            address boundSender,
            bytes32 boundAction
        ) = abi.decode(publicValues, (bool, bytes32, bytes32, bytes32, address, bytes32));

        if (!valid) revert ProofVerificationFailed();
        if (proofFedRoot != federationRoot) revert InvalidProofOutputs();
        if (proofPredHash != predicateHash) revert InvalidProofOutputs();
        if (boundSender != msg.sender) revert SenderBindingMismatch(boundSender, msg.sender);
        if (boundAction != expectedAction) revert ActionBindingMismatch(boundAction, expectedAction);

        nullifier = nf;
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
