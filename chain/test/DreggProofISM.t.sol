// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggProofISM} from "../contracts/DreggProofISM.sol";
import {IInterchainSecurityModule} from "../contracts/IInterchainSecurityModule.sol";
import {DreggPeerRegistry} from "../contracts/DreggPeerRegistry.sol";
import {IDreggPeerRegistry} from "../contracts/IDreggPeerRegistry.sol";
import {AcceptingPeerVerifier} from "./DreggPeerRegistry.t.sol";

/// The ISM now binds an INBOUND message to a PROVEN PEER ROOT (the finalized root
/// of the message's source chain, established by verifying that chain's
/// light-client-STARK-Groth16 in `DreggPeerRegistry`). This is a REAL, live
/// binding — unlike the prior `isProvenMessageRoot` stub that was fail-closed
/// forever. The tests submit a genuine peer finality (the accepting peer verifier
/// stands in for the pairing) whose proven root IS the keccak message-tree root,
/// then verify inclusion under it end-to-end.
contract DreggProofISMTest is Test {
    uint256 constant ETH = 1;
    uint256 constant BASE = 8453;
    bytes32 constant VK_HASH = keccak256("dregg-peer-lightclient-vk-v1");
    uint64 constant HEIGHT = 21_000_000;

    AcceptingPeerVerifier verifier;
    DreggPeerRegistry peers;
    DreggProofISM ism;

    function setUp() public {
        verifier = new AcceptingPeerVerifier();
        peers = new DreggPeerRegistry(verifier, VK_HASH);
        ism = new DreggProofISM(peers);
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    /// Record `root` as a proven finalized root of chain `chainId` at a fresh
    /// height, by submitting a (mock-verified) peer finality proof. This is the
    /// REAL binding surface — no vm.mockCall.
    uint64 private _nextHeight = HEIGHT;
    function proveRoot(uint256 chainId, bytes32 root) internal {
        peers.submitPeerFinality(
            chainId, _nextHeight++, root,
            [uint256(1), uint256(2)],
            [[uint256(3), uint256(4)], [uint256(5), uint256(6)]],
            [uint256(7), uint256(8)],
            [uint256(9), uint256(10)],
            [uint256(11), uint256(12)]
        );
    }

    /// Mirror of the contract's position-indexed fold, used to BUILD fixtures.
    function _fold(bytes32 leaf, bytes32[] memory proof, uint256 index)
        internal
        pure
        returns (bytes32)
    {
        bytes32 node = leaf;
        uint256 idx = index;
        for (uint256 i = 0; i < proof.length; i++) {
            if (idx & 1 == 0) {
                node = keccak256(abi.encodePacked(node, proof[i]));
            } else {
                node = keccak256(abi.encodePacked(proof[i], node));
            }
            idx >>= 1;
        }
        return node;
    }

    function _meta(uint256 chainId, bytes32 root, bytes32[] memory proof, uint256 index)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encode(chainId, root, proof, index);
    }

    // A canonical 4-leaf keccak Merkle tree over four messages.
    function _tree4()
        internal
        pure
        returns (bytes32 root, bytes32 l0, bytes32 l3, bytes32 n01, bytes32 n23)
    {
        l0 = keccak256("hyperlane message zero");
        bytes32 l1 = keccak256("hyperlane message one");
        bytes32 l2 = keccak256("hyperlane message two");
        l3 = keccak256("hyperlane message three");
        n01 = keccak256(abi.encodePacked(l0, l1));
        n23 = keccak256(abi.encodePacked(l2, l3));
        root = keccak256(abi.encodePacked(n01, n23));
    }

    // ==================================================================
    // moduleType
    // ==================================================================

    function test_ModuleType_IsNull() public view {
        assertEq(ism.moduleType(), uint8(IInterchainSecurityModule.Types.NULL));
        assertEq(ism.moduleType(), 6);
    }

    // ==================================================================
    // ACCEPT — inclusion machinery under a genuinely-proven peer root
    // ==================================================================

    /// A single-leaf tree whose root == the message leaf. Prove it via the peer
    /// registry; verify with an empty proof.
    function test_Verify_AcceptsSingleLeaf() public {
        bytes memory message = "a lone cross-chain message";
        bytes32 leaf = keccak256(message);
        proveRoot(ETH, leaf); // root == leaf
        bytes32[] memory proof = new bytes32[](0);
        assertTrue(ism.verify(_meta(ETH, leaf, proof, 0), message));
    }

    /// Build a real 4-leaf keccak tree, prove its root as ETH's finalized root,
    /// and verify inclusion of leaf 0 (index 0) and leaf 3 (index 3) through the
    /// ISM's position-indexed fold — the multi-level path.
    function test_Verify_AcceptsMultiLeafInclusion() public {
        (bytes32 root, bytes32 l0, bytes32 l3, bytes32 n01, bytes32 n23) = _tree4();
        proveRoot(ETH, root);
        assertTrue(peers.isProvenPeerRoot(ETH, root));

        // leaf 0, index 0b00: proof = [l1, n23]
        bytes32[] memory p0 = new bytes32[](2);
        p0[0] = keccak256("hyperlane message one");
        p0[1] = n23;
        assertEq(_fold(l0, p0, 0), root); // fixture sanity
        assertTrue(ism.verify(_meta(ETH, root, p0, 0), "hyperlane message zero"));

        // leaf 3, index 0b11: proof = [l2, n01]
        bytes32[] memory p3 = new bytes32[](2);
        p3[0] = keccak256("hyperlane message two");
        p3[1] = n01;
        assertEq(_fold(l3, p3, 3), root);
        assertTrue(ism.verify(_meta(ETH, root, p3, 3), "hyperlane message three"));
    }

    // ==================================================================
    // REJECT — THE NOMAD LAW (the single most important test)
    // ==================================================================

    /// The zero/default root MUST be rejected. isProvenPeerRoot(_, 0) is always
    /// false, so the accept path's first gate reverts — even with an empty proof
    /// (computed root == leaf). This is the exact class of bug that cost Nomad $190M.
    function test_Verify_Reject_ZeroRoot_NomadLaw() public {
        proveRoot(ETH, keccak256("some real root")); // registry non-empty
        bytes32[] memory proof = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, ETH, bytes32(0))
        );
        ism.verify(_meta(ETH, bytes32(0), proof, 0), bytes("anything"));
    }

    // ==================================================================
    // REJECT — unproven (but non-zero) root
    // ==================================================================

    function test_Verify_Reject_UnprovenRoot() public {
        proveRoot(ETH, keccak256("proven root A"));
        bytes32 stranger = keccak256("never proven root B");
        assertFalse(peers.isProvenPeerRoot(ETH, stranger));
        bytes32[] memory proof = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, ETH, stranger)
        );
        ism.verify(_meta(ETH, stranger, proof, 0), bytes("anything"));
    }

    /// Chain-scoped: a root proven for ETH is NOT proven for Base. A message
    /// claiming the wrong source chain is rejected even with a real root + proof.
    function test_Verify_Reject_WrongSourceChain() public {
        bytes memory message = "a cross-chain message";
        bytes32 leaf = keccak256(message);
        proveRoot(ETH, leaf); // proven for ETH only
        assertFalse(peers.isProvenPeerRoot(BASE, leaf));
        bytes32[] memory proof = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, BASE, leaf)
        );
        ism.verify(_meta(BASE, leaf, proof, 0), message);
    }

    // ==================================================================
    // REJECT — inclusion failures (root proven, but leaf not under it)
    // ==================================================================

    /// A tampered sibling: the fold no longer reaches the proven root.
    function test_Verify_Reject_TamperedProof() public {
        (bytes32 root, bytes32 l0, , , bytes32 n23) = _tree4();
        proveRoot(ETH, root);

        bytes32[] memory bad = new bytes32[](2);
        bad[0] = keccak256("hyperlane message one") ^ bytes32(uint256(1)); // flip a bit
        bad[1] = n23;
        bytes32 computed = _fold(l0, bad, 0);
        assertTrue(computed != root);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.InclusionProofInvalid.selector, root, computed
            )
        );
        ism.verify(_meta(ETH, root, bad, 0), "hyperlane message zero");
    }

    /// Correct siblings, WRONG index: position-indexing takes the other branch.
    function test_Verify_Reject_WrongIndex() public {
        (bytes32 root, bytes32 l0, , , bytes32 n23) = _tree4();
        proveRoot(ETH, root);

        bytes32[] memory p0 = new bytes32[](2);
        p0[0] = keccak256("hyperlane message one");
        p0[1] = n23;
        bytes32 computed = _fold(l0, p0, 1); // correct index is 0
        assertTrue(computed != root);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.InclusionProofInvalid.selector, root, computed
            )
        );
        ism.verify(_meta(ETH, root, p0, 1), "hyperlane message zero");
    }

    /// A leaf not in the tree, with an otherwise-valid-shaped proof.
    function test_Verify_Reject_LeafNotUnderRoot() public {
        (bytes32 root, , , , bytes32 n23) = _tree4();
        proveRoot(ETH, root);

        bytes memory forged = "a message that was never committed";
        bytes32[] memory p0 = new bytes32[](2);
        p0[0] = keccak256("hyperlane message one");
        p0[1] = n23;
        bytes32 computed = _fold(keccak256(forged), p0, 0);
        assertTrue(computed != root);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.InclusionProofInvalid.selector, root, computed
            )
        );
        ism.verify(_meta(ETH, root, p0, 0), forged);
    }

    /// Single-leaf identity, but the message is not the proven preimage.
    function test_Verify_Reject_WrongMessageForProvenRoot() public {
        bytes memory committed = "the committed message";
        bytes32 leaf = keccak256(committed);
        proveRoot(ETH, leaf);

        bytes memory wrong = "not the committed message";
        bytes32 computed = keccak256(wrong);
        assertTrue(computed != leaf);
        bytes32[] memory proof = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.InclusionProofInvalid.selector, leaf, computed
            )
        );
        ism.verify(_meta(ETH, leaf, proof, 0), wrong);
    }

    // ==================================================================
    // REJECT — construction fail-closed (codeless registry)
    // ==================================================================

    function test_Reject_CodelessRegistryAtConstruction() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.PeerRegistryHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggProofISM(IDreggPeerRegistry(address(0xBEEF)));
    }

    function test_Reject_CodelessRegistry_ZeroAddress() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.PeerRegistryHasNoCode.selector, address(0)
            )
        );
        new DreggProofISM(IDreggPeerRegistry(address(0)));
    }

    // ==================================================================
    // Wiring sanity
    // ==================================================================

    function test_PinsPeerRegistry() public view {
        assertEq(address(ism.peers()), address(peers));
    }
}
