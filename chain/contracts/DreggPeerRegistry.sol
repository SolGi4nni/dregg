// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDreggPeerRegistry} from "./IDreggPeerRegistry.sol";
import {IPeerLightClientVerifier} from "./IPeerLightClientVerifier.sol";

/// The PEER-VERIFICATION surface — the on-chain VERIFIER of a foreign chain's
/// finalized state, and the exact mirror of `DreggSettlement`.
///
/// `DreggSettlement` lets a peer chain (Base) verify DREGG's state by checking a
/// Groth16-wrapped STARK. `DreggPeerRegistry` closes the reverse asymmetry: it
/// lets dregg (or any chain hosting this contract) verify a PEER chain's
/// finalized state by checking a light-client-STARK-Groth16 — the "chain X
/// finalized state root R at height H" proof produced by the STARK-ified
/// light client (`eth-lightclient/`, wrapped to Groth16 like dregg's own proof).
/// With both deployed, each chain's on-chain verifier can check the OTHER's
/// consensus proof: TRUE PEERS.
///
/// ## What is proven, and at what resolution (honest)
///
/// A recorded root inherits the security of (1) the peer chain's own consensus,
/// (2) the light-client STARK/FRI floor, and (3) the pinned VK's trusted setup —
/// the SAME floor as `DreggSettlement`. This contract adds exactly the on-chain
/// pairing check + a proven-root registry over it; it invents no trust. The
/// SEMANTICS of the recorded root R (a finalized execution STATE root vs a
/// dedicated outbound-MESSAGE root) is fixed by the pinned peer VK — see the
/// NAMED RESIDUAL on the adapters (`DreggProofISM`/`DreggDVN`): keccak-binary
/// message inclusion under R is sound iff R is a keccak message-commitment root
/// the peer proof exposes (else the inbound leg needs an MPT proof over the state
/// root). This registry is agnostic to that choice: it records whatever 32-byte
/// root the pinned VK attests for (chainId, height).
///
/// ## THE NOMAD LAW
///
/// Nomad lost $190M because an uninitialized slot defaulted to "accepted". Here
/// `bytes32(0)` is NEVER recorded (`submitPeerFinality` reverts `ZeroPeerRoot`),
/// so `isProvenPeerRoot(chainId, 0)` is always false — proven by an explicit test.
///
/// ## Dreggic
///
/// Submission is PERMISSIONLESS and PROOF-GATED: the authority to advance a peer
/// root is the Groth16 proof itself (a capability), never an owner or a
/// committee. Each accepted submission leaves a RECEIPT (`PeerFinalityProven`)
/// recording the exercised proof's claim + the relayer for attribution.
contract DreggPeerRegistry is IDreggPeerRegistry {
    /// BN254 scalar field order R. Every public-input lane must be < R to be a
    /// canonical residue (same constant the wrap verifier enforces).
    uint256 internal constant BN254_R =
        0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;

    /// The pinned peer light-client wrap verifier (VK behind it, ideally the
    /// timelocked VK-epoch registry). Immutable — the trust anchor is fixed at
    /// deployment, never governance-swappable at this layer.
    IPeerLightClientVerifier public immutable verifier;

    bytes32 private immutable _verifyingKeyHash;

    // chainId => root => proven-ever (historical set, like DreggSettlement._provenRoots).
    mapping(uint256 => mapping(bytes32 => bool)) private _provenPeerRoots;
    // chainId => height => finalized root proven at that height.
    mapping(uint256 => mapping(uint64 => bytes32)) private _rootAtHeight;
    // chainId => latest (highest) proven height.
    mapping(uint256 => uint64) private _latestHeight;
    // chainId => latest proven root.
    mapping(uint256 => bytes32) private _latestRoot;

    constructor(IPeerLightClientVerifier verifier_, bytes32 verifyingKeyHash_) {
        // Fail closed: a codeless verifier address must never be pinned (a
        // staticcall to a codeless address "succeeds" returning empty — the exact
        // fail-open pattern the census flagged).
        if (address(verifier_).code.length == 0) {
            revert VerifierHasNoCode(address(verifier_));
        }
        if (verifyingKeyHash_ == bytes32(0)) {
            revert ZeroVerifyingKeyHash();
        }
        verifier = verifier_;
        _verifyingKeyHash = verifyingKeyHash_;
    }

    // ------------------------------------------------------------------
    // Views
    // ------------------------------------------------------------------

    function isProvenPeerRoot(uint256 chainId, bytes32 root)
        external
        view
        returns (bool)
    {
        // THE NOMAD LAW made explicit (the mapping default is already false, but
        // the zero root is rejected without a storage read — never "defaults to
        // accepted").
        if (root == bytes32(0)) return false;
        return _provenPeerRoots[chainId][root];
    }

    function provenPeerRoot(uint256 chainId, uint64 height)
        external
        view
        returns (bytes32)
    {
        return _rootAtHeight[chainId][height];
    }

    function latestPeerRoot(uint256 chainId) external view returns (bytes32) {
        return _latestRoot[chainId];
    }

    function latestPeerHeight(uint256 chainId) external view returns (uint64) {
        return _latestHeight[chainId];
    }

    function verifyingKeyHash() external view returns (bytes32) {
        return _verifyingKeyHash;
    }

    /// The two 128-bit halves of a 32-byte root, the pinned public-input encoding
    /// (rootHi = top 128 bits, rootLo = bottom 128 bits). Exposed for off-chain
    /// tooling / proof construction to match the on-chain assembly exactly.
    function splitRoot(bytes32 root) public pure returns (uint256 hi, uint256 lo) {
        uint256 r = uint256(root);
        hi = r >> 128;
        lo = r & ((uint256(1) << 128) - 1);
    }

    // ------------------------------------------------------------------
    // Submission (permissionless; the proof is the capability)
    // ------------------------------------------------------------------

    function submitPeerFinality(
        uint256 srcChainId,
        uint64 height,
        bytes32 finalizedRoot,
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok
    ) external {
        // 0. Fail-closed well-formedness. Zero chain / zero root are never valid
        //    (THE NOMAD LAW for the root); a non-canonical chainId cannot be a
        //    public-input lane.
        if (srcChainId == 0) revert ZeroChainId();
        if (finalizedRoot == bytes32(0)) revert ZeroPeerRoot();
        if (srcChainId >= BN254_R) revert NonCanonicalChainId(srcChainId);

        // 1. Monotone finality: a peer's proven height only advances. Rejects a
        //    stale or replayed proof at an already-proven (or lower) height.
        uint64 latest = _latestHeight[srcChainId];
        bytes32 oldRoot = _latestRoot[srcChainId];
        // Distinguish "nothing proven yet" (oldRoot == 0) from "genesis at height
        // 0": the first submission for a chain may land at any height; every later
        // one must strictly exceed the latest.
        if (oldRoot != bytes32(0) && height <= latest) {
            revert NonMonotoneHeight(srcChainId, height, latest);
        }

        // 2. Assemble the pinned 4-lane public-input vector [chainId, height,
        //    rootHi, rootLo]. height (uint64) and the two 128-bit halves are
        //    always < BN254_R; chainId was bounded above.
        (uint256 rootHi, uint256 rootLo) = splitRoot(finalizedRoot);
        uint256[4] memory inputs;
        inputs[0] = srcChainId;
        inputs[1] = uint256(height);
        inputs[2] = rootHi;
        inputs[3] = rootLo;

        // 3. The pairing check over the pinned peer VK. A false return OR a revert
        //    OR a codeless verifier all reject (fail closed) — this is where a
        //    forged proof, a wrong-statement proof, or a proof for a DIFFERENT
        //    (chainId, height, root) triple than claimed is rejected, because the
        //    triple is bound into the public inputs the verifier checks.
        if (!verifier.verifyProof(a, b, c, commitments, commitmentPok, inputs)) {
            revert ProofRejected();
        }

        // 4. Record. Historical roots stay proven (the set is never pruned), so a
        //    message committed under a since-superseded root still verifies.
        _provenPeerRoots[srcChainId][finalizedRoot] = true;
        _rootAtHeight[srcChainId][height] = finalizedRoot;
        _latestHeight[srcChainId] = height;
        _latestRoot[srcChainId] = finalizedRoot;

        emit PeerFinalityProven(srcChainId, height, finalizedRoot, msg.sender);
        emit PeerRootAdvanced(srcChainId, oldRoot, finalizedRoot, height);
    }
}
