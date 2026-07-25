// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggPeerRegistry} from "../contracts/DreggPeerRegistry.sol";
import {IDreggPeerRegistry} from "../contracts/IDreggPeerRegistry.sol";
import {IPeerLightClientVerifier} from "../contracts/IPeerLightClientVerifier.sol";

/// A peer light-client wrap verifier that ALWAYS accepts — so the real
/// `DreggPeerRegistry` state machine (monotone finality, the proven-root set, the
/// receipt) can be exercised without a real gnark proof. The pairing SOUNDNESS
/// itself is the pinned verifier's job (its dregg twin is exercised against a
/// real fixture in DreggSettlementRealProof.t.sol); here a false-returning verifier
/// stands in for a forged proof.
contract AcceptingPeerVerifier is IPeerLightClientVerifier {
    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[4] calldata
    ) external pure returns (bool) {
        return true;
    }
}

/// A verifier standing in for a FORGED / wrong-statement proof: always false.
contract RejectingPeerVerifier is IPeerLightClientVerifier {
    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[4] calldata
    ) external pure returns (bool) {
        return false;
    }
}

/// A verifier that accepts ONLY when the public inputs the registry assembled
/// equal a pinned [chainId, height, rootHi, rootLo]. This is the on-chain twin of
/// a real Groth16 whose statement binds exactly that triple: it proves the
/// registry threads (srcChainId, height, finalizedRoot) into the right lanes, so
/// a proof for one triple cannot be recorded under another. A REAL Groth16
/// rejects a mismatched public input the same way (a wrong lane => wrong MSM =>
/// failed pairing); this mock makes that binding checkable without a fixture.
contract LaneCheckingPeerVerifier is IPeerLightClientVerifier {
    uint256 public immutable eChainId;
    uint256 public immutable eHeight;
    uint256 public immutable eRootHi;
    uint256 public immutable eRootLo;

    constructor(uint256 chainId_, uint256 height_, uint256 rootHi_, uint256 rootLo_) {
        eChainId = chainId_;
        eHeight = height_;
        eRootHi = rootHi_;
        eRootLo = rootLo_;
    }

    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[4] calldata publicInputs
    ) external view returns (bool) {
        return publicInputs[0] == eChainId
            && publicInputs[1] == eHeight
            && publicInputs[2] == eRootHi
            && publicInputs[3] == eRootLo;
    }
}

contract DreggPeerRegistryTest is Test {
    bytes32 constant VK_HASH = keccak256("dregg-peer-lightclient-vk-v1");
    uint256 constant ETH = 1; // ETH mainnet
    uint256 constant BASE = 8453; // Base
    uint256 internal constant BN254_R =
        0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;

    AcceptingPeerVerifier verifier;
    DreggPeerRegistry reg;

    // Re-declared for vm.expectEmit (topic hashes match the contract's).
    event PeerFinalityProven(
        uint256 indexed srcChainId,
        uint64 indexed height,
        bytes32 indexed finalizedRoot,
        address relayer
    );
    event PeerRootAdvanced(
        uint256 indexed srcChainId,
        bytes32 oldRoot,
        bytes32 newRoot,
        uint64 height
    );

    function setUp() public {
        verifier = new AcceptingPeerVerifier();
        reg = new DreggPeerRegistry(verifier, VK_HASH);
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    // Dummy Groth16 proof words — the mock verifier ignores them.
    function _a() internal pure returns (uint256[2] memory) {
        return [uint256(1), uint256(2)];
    }
    function _b() internal pure returns (uint256[2][2] memory) {
        return [[uint256(3), uint256(4)], [uint256(5), uint256(6)]];
    }
    function _c() internal pure returns (uint256[2] memory) {
        return [uint256(7), uint256(8)];
    }
    function _cm() internal pure returns (uint256[2] memory) {
        return [uint256(9), uint256(10)];
    }
    function _pok() internal pure returns (uint256[2] memory) {
        return [uint256(11), uint256(12)];
    }

    function _submit(uint256 chainId, uint64 height, bytes32 root) internal {
        reg.submitPeerFinality(chainId, height, root, _a(), _b(), _c(), _cm(), _pok());
    }

    function _submitTo(
        DreggPeerRegistry r,
        uint256 chainId,
        uint64 height,
        bytes32 root
    ) internal {
        r.submitPeerFinality(chainId, height, root, _a(), _b(), _c(), _cm(), _pok());
    }

    // ==================================================================
    // ACCEPT — a peer-state proof verifies and is recorded
    // ==================================================================

    function test_Accept_RecordsProvenPeerRoot() public {
        bytes32 root = keccak256("eth finalized state root @ 21000000");
        uint64 h = 21_000_000;

        (uint256 hi, uint256 lo) = reg.splitRoot(root);
        vm.expectEmit(true, true, true, true, address(reg));
        emit PeerFinalityProven(ETH, h, root, address(this));
        vm.expectEmit(true, false, false, true, address(reg));
        emit PeerRootAdvanced(ETH, bytes32(0), root, h);

        _submit(ETH, h, root);

        assertTrue(reg.isProvenPeerRoot(ETH, root));
        assertEq(reg.provenPeerRoot(ETH, h), root);
        assertEq(reg.latestPeerRoot(ETH), root);
        assertEq(reg.latestPeerHeight(ETH), h);
        assertEq(reg.verifyingKeyHash(), VK_HASH);
        // splitRoot recomposes the full 256-bit root (no truncation).
        assertEq(bytes32((hi << 128) | lo), root);
    }

    /// The proof BINDS the triple: with a verifier that only accepts a pinned
    /// [chainId, height, rootHi, rootLo], the matching submission succeeds but any
    /// other triple is rejected — the registry threads the args into the right lanes.
    function test_Binding_PublicInputsBoundToTriple() public {
        bytes32 root = keccak256("bound root");
        uint64 h = 500;
        (uint256 hi, uint256 lo) = reg.splitRoot(root);

        LaneCheckingPeerVerifier lv = new LaneCheckingPeerVerifier(ETH, h, hi, lo);
        DreggPeerRegistry r = new DreggPeerRegistry(lv, VK_HASH);

        // Exact triple → accepted.
        _submitTo(r, ETH, h, root);
        assertTrue(r.isProvenPeerRoot(ETH, root));

        // Wrong chainId for the same (height, root) → verifier rejects.
        vm.expectRevert(IDreggPeerRegistry.ProofRejected.selector);
        _submitTo(r, BASE, h + 1, root);

        // Wrong root for the same (chainId) at a higher height → verifier rejects.
        vm.expectRevert(IDreggPeerRegistry.ProofRejected.selector);
        _submitTo(r, ETH, h + 1, keccak256("some other root"));
    }

    /// A historical root stays proven after a higher height supersedes it (the
    /// dispatch-time semantics a cross-chain verifier needs).
    function test_Accept_HistoricalRootStaysProven() public {
        bytes32 rootA = keccak256("eth root @ 10");
        bytes32 rootB = keccak256("eth root @ 20");
        _submit(ETH, 10, rootA);
        _submit(ETH, 20, rootB);

        assertTrue(reg.isProvenPeerRoot(ETH, rootA)); // still queryable
        assertTrue(reg.isProvenPeerRoot(ETH, rootB));
        assertEq(reg.latestPeerRoot(ETH), rootB);
        assertEq(reg.latestPeerHeight(ETH), 20);
        assertEq(reg.provenPeerRoot(ETH, 10), rootA);
    }

    /// Roots are keyed by chainId: a root proven for ETH is NOT proven for Base.
    function test_Accept_ChainIsolation() public {
        bytes32 root = keccak256("a root");
        _submit(ETH, 100, root);
        assertTrue(reg.isProvenPeerRoot(ETH, root));
        assertFalse(reg.isProvenPeerRoot(BASE, root));
        assertEq(reg.latestPeerRoot(BASE), bytes32(0));
    }

    /// The first submission for a chain may land at height 0 (genesis anchor).
    function test_Accept_FirstSubmissionAtHeightZero() public {
        bytes32 root = keccak256("genesis");
        _submit(ETH, 0, root);
        assertTrue(reg.isProvenPeerRoot(ETH, root));
        assertEq(reg.provenPeerRoot(ETH, 0), root);
        // ...but a second submission at height 0 no longer strictly advances.
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggPeerRegistry.NonMonotoneHeight.selector, ETH, uint64(0), uint64(0)
            )
        );
        _submit(ETH, 0, keccak256("genesis-2"));
    }

    // ==================================================================
    // REJECT — a forged proof is rejected
    // ==================================================================

    function test_Reject_ForgedProof() public {
        RejectingPeerVerifier rv = new RejectingPeerVerifier();
        DreggPeerRegistry r = new DreggPeerRegistry(rv, VK_HASH);

        vm.expectRevert(IDreggPeerRegistry.ProofRejected.selector);
        _submitTo(r, ETH, 1, keccak256("root under a forged proof"));

        assertFalse(r.isProvenPeerRoot(ETH, keccak256("root under a forged proof")));
    }

    // ==================================================================
    // REJECT — THE NOMAD LAW (zero root never recorded / accepted)
    // ==================================================================

    function test_Nomad_ZeroRootNeverRecorded() public {
        vm.expectRevert(IDreggPeerRegistry.ZeroPeerRoot.selector);
        _submit(ETH, 1, bytes32(0));
        // ...and querying the zero root is always false.
        assertFalse(reg.isProvenPeerRoot(ETH, bytes32(0)));
    }

    function test_Nomad_IsProvenPeerRootZero_AlwaysFalse() public {
        // Even after a real proven root exists, the zero root stays false.
        _submit(ETH, 1, keccak256("real"));
        assertFalse(reg.isProvenPeerRoot(ETH, bytes32(0)));
    }

    // ==================================================================
    // REJECT — malformed submissions
    // ==================================================================

    function test_Reject_ZeroChainId() public {
        vm.expectRevert(IDreggPeerRegistry.ZeroChainId.selector);
        _submit(0, 1, keccak256("root"));
    }

    function test_Reject_NonCanonicalChainId() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggPeerRegistry.NonCanonicalChainId.selector, BN254_R
            )
        );
        _submit(BN254_R, 1, keccak256("root"));
    }

    function test_Reject_NonMonotoneHeight_Equal() public {
        _submit(ETH, 100, keccak256("root @ 100"));
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggPeerRegistry.NonMonotoneHeight.selector, ETH, uint64(100), uint64(100)
            )
        );
        _submit(ETH, 100, keccak256("another root @ 100"));
    }

    function test_Reject_NonMonotoneHeight_Lower() public {
        _submit(ETH, 100, keccak256("root @ 100"));
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggPeerRegistry.NonMonotoneHeight.selector, ETH, uint64(50), uint64(100)
            )
        );
        _submit(ETH, 50, keccak256("stale root @ 50"));
    }

    function test_Accept_MonotoneAdvance() public {
        _submit(ETH, 100, keccak256("root @ 100"));
        _submit(ETH, 101, keccak256("root @ 101"));
        assertEq(reg.latestPeerHeight(ETH), 101);
    }

    // ==================================================================
    // REJECT — construction fail-closed
    // ==================================================================

    function test_Reject_CodelessVerifierAtConstruction() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggPeerRegistry.VerifierHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggPeerRegistry(IPeerLightClientVerifier(address(0xBEEF)), VK_HASH);
    }

    function test_Reject_ZeroVerifyingKeyHash() public {
        vm.expectRevert(IDreggPeerRegistry.ZeroVerifyingKeyHash.selector);
        new DreggPeerRegistry(verifier, bytes32(0));
    }

    // ==================================================================
    // Wiring sanity
    // ==================================================================

    function test_PinsVerifier() public view {
        assertEq(address(reg.verifier()), address(verifier));
    }
}
