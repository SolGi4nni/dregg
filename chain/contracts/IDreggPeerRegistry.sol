// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// The PEER-VERIFICATION query surface — the mirror of `IDreggSettlement` for a
/// FOREIGN chain's finalized state.
///
/// `DreggSettlement` answers "has dregg proven state root R?" (`isProvenRoot`);
/// this answers "has a PEER chain X proven finalized root R?"
/// (`isProvenPeerRoot`). A `DreggPeerRegistry` establishes each answer by
/// verifying a light-client-STARK-Groth16 against a pinned verification key —
/// the same crypto discipline as settlement, pointed at the other direction.
/// Together they make each chain an on-chain verifier of the OTHER's consensus:
/// TRUE PEERS.
///
/// Cross-chain adapters (Hyperlane ISM, LayerZero DVN) gate an INBOUND message's
/// acceptance on `isProvenPeerRoot(srcChainId, root)` + a Merkle inclusion under
/// `root`, so a message from chain X is attested iff it is included under a root
/// that a light-client proof has established as chain X's finalized commitment.
interface IDreggPeerRegistry {
    // ------------------------------------------------------------------
    // Errors (all reject paths are typed; the contract fails closed)
    // ------------------------------------------------------------------

    /// The peer light-client verifier pinned at construction has no code
    /// (a staticcall to a codeless address "succeeds" — the census fail-open shape).
    error VerifierHasNoCode(address verifier);

    /// The expected verifying-key hash pinned at construction is zero.
    error ZeroVerifyingKeyHash();

    /// `chainId == 0`: the zero chain is never a valid peer (fail closed).
    error ZeroChainId();

    /// `finalizedRoot == 0`: THE NOMAD LAW — the zero/default root is never
    /// recorded, so `isProvenPeerRoot(chainId, 0)` is always false.
    error ZeroPeerRoot();

    /// `chainId` is not a canonical BN254 scalar-field residue, so it cannot be a
    /// well-formed public-input lane.
    error NonCanonicalChainId(uint256 chainId);

    /// A submitted finality does not strictly advance the peer's proven height:
    /// `height <= latestPeerHeight(chainId)`. Finality only moves forward.
    error NonMonotoneHeight(uint256 chainId, uint64 submitted, uint64 latest);

    /// The peer light-client verifier returned false for the pairing check
    /// (a forged / malformed / wrong-statement proof).
    error ProofRejected();

    // ------------------------------------------------------------------
    // Events (receipt-shaped — the authority is the PROOF, the relayer is
    // recorded for attribution, never as the authority)
    // ------------------------------------------------------------------

    /// A peer finality proof was verified and recorded. This is the receipt: it
    /// names WHAT was proven (chainId, height, finalizedRoot) and WHO relayed the
    /// proof (attribution only — submission is permissionless, gated by the proof
    /// itself, not by `relayer`).
    event PeerFinalityProven(
        uint256 indexed srcChainId,
        uint64 indexed height,
        bytes32 indexed finalizedRoot,
        address relayer
    );

    /// The peer's latest proven root advanced from `oldRoot` to `newRoot`.
    event PeerRootAdvanced(
        uint256 indexed srcChainId,
        bytes32 oldRoot,
        bytes32 newRoot,
        uint64 height
    );

    /// THE CAPABILITY RECEIPT. Where `PeerFinalityProven` records WHAT finalized,
    /// this binds the exercised proof's `proofDigest` (the keccak fingerprint of
    /// the Groth16 proof object that was just verified) to the exact
    /// `(srcChainId, height, finalizedRoot)` triple it authorized. The proof is
    /// the authority (a capability); this receipt is the on-chain trace of that
    /// capability being exercised — auditable to the specific proof object, not to
    /// an owner or a committee. `relayer` is attribution only (submission is
    /// permissionless). A downstream indexer can match this digest to the proof it
    /// saw relayed and confirm no root advanced without a proof behind it.
    event PeerProofReceipt(
        uint256 indexed srcChainId,
        uint64 indexed height,
        bytes32 indexed finalizedRoot,
        bytes32 proofDigest,
        address relayer
    );

    // ------------------------------------------------------------------
    // Views
    // ------------------------------------------------------------------

    /// True iff `root` has ever been proven as a finalized root of peer `chainId`
    /// (any historical proven height — a since-superseded root still verifies, so
    /// a message committed under a dispatch-time root still checks). Keyed by
    /// chainId, so a root proven for one chain is NOT proven for another.
    /// `isProvenPeerRoot(chainId, 0)` is always false (THE NOMAD LAW).
    function isProvenPeerRoot(uint256 chainId, bytes32 root) external view returns (bool);

    /// The finalized root proven for peer `chainId` at `height`, or bytes32(0) if
    /// no finality has been proven at that height.
    function provenPeerRoot(uint256 chainId, uint64 height) external view returns (bytes32);

    /// The latest (highest-height) proven finalized root for peer `chainId`, or
    /// bytes32(0) if none.
    function latestPeerRoot(uint256 chainId) external view returns (bytes32);

    /// The highest proven height for peer `chainId` (0 if none proven; use
    /// `latestPeerRoot != 0` to distinguish "none" from "genesis at height 0").
    function latestPeerHeight(uint256 chainId) external view returns (uint64);

    /// keccak256 of the Groth16 verifying key this registry checks peer proofs
    /// against — the on-chain commitment to the peer wrap circuit's VK.
    function verifyingKeyHash() external view returns (bytes32);

    // ------------------------------------------------------------------
    // Submission (permissionless: the authority is the proof)
    // ------------------------------------------------------------------

    /// Submit a peer-finality proof "chain `srcChainId` finalized `finalizedRoot`
    /// at `height`". Verifies the Groth16 over the pinned peer VK against the
    /// 4-lane public-input vector [chainId, height, rootHi, rootLo] assembled from
    /// these arguments, then records the proven root. Permissionless — anyone
    /// holding a valid proof may advance the peer root (the proof IS the
    /// capability). Reverts on a zero chainId/root, a non-monotone height, or a
    /// failed pairing check.
    function submitPeerFinality(
        uint256 srcChainId,
        uint64 height,
        bytes32 finalizedRoot,
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok
    ) external;
}
