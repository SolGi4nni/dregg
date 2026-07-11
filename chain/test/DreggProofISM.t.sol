// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggProofISM} from "../contracts/DreggProofISM.sol";
import {IInterchainSecurityModule} from "../contracts/IInterchainSecurityModule.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";

/// Mock Groth16 verifier — always accepts, so the REAL DreggSettlement can be
/// driven to record message roots in setUp/tests. (Groth16 soundness is
/// exercised in DreggSettlement.t.sol; here we only need real settlements so the
/// message-root registry is genuine, not a stub.)
contract AcceptingVerifier25 is IGroth16Verifier25 {
    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[25] calldata
    ) external pure returns (bool) {
        return true;
    }
}

contract DreggProofISMTest is Test {
    uint32 constant P = 2013265921; // BabyBear prime
    bytes32 constant VK_HASH = keccak256("dregg-settlement-vk-v1");

    AcceptingVerifier25 verifier;
    DreggSettlement settlement;
    DreggProofISM ism;

    function setUp() public {
        verifier = new AcceptingVerifier25();
        settlement = new DreggSettlement(verifier, VK_HASH, mkLanes(1));
        ism = new DreggProofISM(settlement);
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    function mkLanes(uint32 seed) internal pure returns (uint32[8] memory l) {
        for (uint32 i = 0; i < 8; i++) {
            l[i] = (seed * 7919 + i * 104729 + 1) % P;
        }
    }

    /// Advance the REAL settlement one span (genesis -> mkLanes(2)) recording
    /// `msgRoot` as an outbound message root. After this,
    /// settlement.isProvenMessageRoot(msgRoot) is true (for msgRoot != 0).
    function recordMsgRoot(bytes32 msgRoot) internal {
        settlement.settle(
            [uint256(1), uint256(2)],
            [[uint256(3), uint256(4)], [uint256(5), uint256(6)]],
            [uint256(7), uint256(8)],
            mkLanes(1), mkLanes(2), 7, mkLanes(3),
            msgRoot
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

    function _meta(bytes32 root, bytes32[] memory proof, uint256 index)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encode(root, proof, index);
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
    // ACCEPT — against the REAL DreggSettlement message-root registry
    // ==================================================================

    /// A single-leaf tree whose root == the message leaf. Record it as a message
    /// root on the real settlement; verify with an empty proof.
    function test_Verify_AcceptsSingleLeaf() public {
        bytes memory message = "a lone cross-chain message";
        bytes32 leaf = keccak256(message);
        recordMsgRoot(leaf); // root == leaf
        bytes32[] memory proof = new bytes32[](0);
        assertTrue(ism.verify(_meta(leaf, proof, 0), message));
    }

    /// Build a real 4-leaf keccak tree, record its root on the REAL settlement,
    /// and verify inclusion of leaf 0 (index 0) and leaf 3 (index 3) through the
    /// ISM's position-indexed fold — the multi-level path against the real oracle.
    function test_Verify_AcceptsMultiLeafInclusion() public {
        (bytes32 root, bytes32 l0, bytes32 l3, bytes32 n01, bytes32 n23) = _tree4();
        recordMsgRoot(root);
        assertTrue(settlement.isProvenMessageRoot(root));

        // leaf 0, index 0b00: proof = [l1, n23]
        bytes32[] memory p0 = new bytes32[](2);
        p0[0] = keccak256("hyperlane message one");
        p0[1] = n23;
        assertEq(_fold(l0, p0, 0), root); // fixture sanity
        assertTrue(ism.verify(_meta(root, p0, 0), "hyperlane message zero"));

        // leaf 3, index 0b11: proof = [l2, n01]
        bytes32[] memory p3 = new bytes32[](2);
        p3[0] = keccak256("hyperlane message two");
        p3[1] = n01;
        assertEq(_fold(l3, p3, 3), root);
        assertTrue(ism.verify(_meta(root, p3, 3), "hyperlane message three"));
    }

    // ==================================================================
    // REJECT — THE NOMAD LAW (the single most important test)
    // ==================================================================

    /// The zero/default message root MUST be rejected. isProvenMessageRoot(0) is
    /// always false, so the accept path's first gate reverts — even with an empty
    /// proof (computed root == leaf). This is the exact class of bug that cost
    /// Nomad $190M. Proven against the REAL settlement.
    function test_Verify_Reject_ZeroRoot_NomadLaw() public {
        recordMsgRoot(keccak256("some real message root")); // registry non-empty
        bytes32[] memory proof = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, bytes32(0))
        );
        ism.verify(_meta(bytes32(0), proof, 0), bytes("anything"));
    }

    // ==================================================================
    // REJECT — unproven (but non-zero) root
    // ==================================================================

    function test_Verify_Reject_UnrecordedRoot() public {
        recordMsgRoot(keccak256("recorded root A"));
        bytes32 stranger = keccak256("never recorded root B");
        assertFalse(settlement.isProvenMessageRoot(stranger));
        bytes32[] memory proof = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(DreggProofISM.UnprovenRoot.selector, stranger)
        );
        ism.verify(_meta(stranger, proof, 0), bytes("anything"));
    }

    // ==================================================================
    // REJECT — inclusion failures (root recorded, but leaf not under it)
    // ==================================================================

    /// A tampered sibling: the fold no longer reaches the recorded root.
    function test_Verify_Reject_TamperedProof() public {
        (bytes32 root, bytes32 l0, , , bytes32 n23) = _tree4();
        recordMsgRoot(root);

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
        ism.verify(_meta(root, bad, 0), "hyperlane message zero");
    }

    /// Correct siblings, WRONG index: position-indexing takes the other branch.
    function test_Verify_Reject_WrongIndex() public {
        (bytes32 root, bytes32 l0, , , bytes32 n23) = _tree4();
        recordMsgRoot(root);

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
        ism.verify(_meta(root, p0, 1), "hyperlane message zero");
    }

    /// A leaf not in the tree, with an otherwise-valid-shaped proof.
    function test_Verify_Reject_LeafNotUnderRoot() public {
        (bytes32 root, , , , bytes32 n23) = _tree4();
        recordMsgRoot(root);

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
        ism.verify(_meta(root, p0, 0), forged);
    }

    /// Single-leaf identity, but the message is not the recorded preimage.
    function test_Verify_Reject_WrongMessageForRecordedRoot() public {
        bytes memory committed = "the committed message";
        bytes32 leaf = keccak256(committed);
        recordMsgRoot(leaf);

        bytes memory wrong = "not the committed message";
        bytes32 computed = keccak256(wrong);
        assertTrue(computed != leaf);
        bytes32[] memory proof = new bytes32[](0);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.InclusionProofInvalid.selector, leaf, computed
            )
        );
        ism.verify(_meta(leaf, proof, 0), wrong);
    }

    // ==================================================================
    // REJECT — construction fail-closed (codeless settlement)
    // ==================================================================

    function test_Reject_CodelessSettlementAtConstruction() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.SettlementHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggProofISM(IDreggSettlement(address(0xBEEF)));
    }

    function test_Reject_CodelessSettlement_ZeroAddress() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofISM.SettlementHasNoCode.selector, address(0)
            )
        );
        new DreggProofISM(IDreggSettlement(address(0)));
    }

    // ==================================================================
    // Wiring sanity
    // ==================================================================

    function test_PinsSettlement() public view {
        assertEq(address(ism.settlement()), address(settlement));
    }
}
