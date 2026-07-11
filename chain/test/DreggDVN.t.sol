// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggDVN} from "../contracts/DreggDVN.sol";
import {IReceiveUln} from "../contracts/ILayerZeroDVN.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";

/// Always-true Groth16 mock: `setUp` only needs the real `DreggSettlement` to
/// accept settles so it records real message roots. The DVN's own gate is
/// `isProvenMessageRoot`, exercised against real settlement state.
contract MockGroth16Verifier25 is IGroth16Verifier25 {
    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[25] calldata
    ) external pure returns (bool) {
        return true;
    }
}

/// Records whether/how the receive-library's `verify` was called. The accept
/// path must call this EXACTLY once with the right args; every reject path must
/// leave it UNCALLED (the fail-closed invariant).
contract MockReceiveUln is IReceiveUln {
    uint256 public verifyCount;
    bytes32 public lastHeaderHash;
    bytes32 public lastPayloadHash;
    uint64 public lastConfirmations;

    function verify(
        bytes calldata packetHeader,
        bytes32 payloadHash,
        uint64 confirmations
    ) external {
        verifyCount++;
        lastHeaderHash = keccak256(packetHeader);
        lastPayloadHash = payloadHash;
        lastConfirmations = confirmations;
    }
}

contract DreggDVNTest is Test {
    MockGroth16Verifier25 verifier;
    MockReceiveUln uln;
    DreggSettlement settlement;
    DreggDVN dvn;

    bytes32 constant VK_HASH = keccak256("dregg-settlement-vk-v1");
    uint32 constant P = 2013265921; // BabyBear prime

    bytes constant HEADER = hex"0102030405060708";
    uint64 constant CONF = 15;

    // Re-declared for vm.expectEmit (topic hashes match DreggDVN's).
    event PayloadAttested(
        bytes32 indexed messageRoot,
        bytes32 indexed payloadHash,
        uint64 confirmations,
        uint256 leafIndex
    );

    function setUp() public {
        verifier = new MockGroth16Verifier25();
        uln = new MockReceiveUln();
        settlement = new DreggSettlement(verifier, VK_HASH, mkLanes(1));
        dvn = new DreggDVN(settlement, uln);
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
    /// `msgRoot`. After this, settlement.isProvenMessageRoot(msgRoot) is true.
    function recordMsgRoot(bytes32 msgRoot) internal {
        settlement.settle(
            [uint256(1), uint256(2)],
            [[uint256(3), uint256(4)], [uint256(5), uint256(6)]],
            [uint256(7), uint256(8)],
            mkLanes(1), mkLanes(2), 10, mkLanes(3),
            msgRoot
        );
    }

    /// Mirror of DreggDVN._hashPair (sorted-pair) so tests can BUILD fixtures.
    function hashPair(bytes32 a, bytes32 b) internal pure returns (bytes32) {
        return a < b
            ? keccak256(abi.encodePacked(a, b))
            : keccak256(abi.encodePacked(b, a));
    }

    function md(bytes32 root, bytes32[] memory proof, uint256 idx)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encode(root, proof, idx);
    }

    function emptyProof() internal pure returns (bytes32[] memory) {
        return new bytes32[](0);
    }

    // A canonical 4-leaf sorted-pair keccak tree over four payload hashes.
    function _tree4()
        internal
        pure
        returns (bytes32 root, bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3)
    {
        l0 = keccak256("layerzero payload zero");
        l1 = keccak256("layerzero payload one");
        l2 = keccak256("layerzero payload two");
        l3 = keccak256("layerzero payload three");
    }

    function _root4(bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3)
        internal
        pure
        returns (bytes32)
    {
        return hashPair(hashPair(l0, l1), hashPair(l2, l3));
    }

    // ------------------------------------------------------------------
    // Accept path (calls the ULN exactly once, right args)
    // ------------------------------------------------------------------

    /// Multi-leaf inclusion under a REAL recorded message root: payload l0 with
    /// proof [l1, hashPair(l2,l3)] climbs to the recorded root => attest once.
    function test_Accept_MultiLeafInclusion_CallsUlnOnce() public {
        (, bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root = _root4(l0, l1, l2, l3);
        recordMsgRoot(root);
        assertTrue(settlement.isProvenMessageRoot(root));

        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l1;
        proof[1] = hashPair(l2, l3);

        vm.expectEmit(true, true, false, true, address(dvn));
        emit PayloadAttested(root, l0, CONF, 0);

        dvn.attestPayload(HEADER, l0, CONF, md(root, proof, 0));

        assertEq(uln.verifyCount(), 1);
        assertEq(uln.lastHeaderHash(), keccak256(HEADER));
        assertEq(uln.lastPayloadHash(), l0);
        assertEq(uln.lastConfirmations(), CONF);
    }

    /// A HISTORICAL recorded root (span 1) still attests after span 2 supersedes
    /// it — the dispatch-time semantics a cross-chain verifier needs.
    function test_Accept_HistoricalMessageRoot() public {
        (, bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root1 = _root4(l0, l1, l2, l3);
        recordMsgRoot(root1); // span 1

        // span 2: chain forward from mkLanes(2), record a different root.
        settlement.settle(
            [uint256(1), uint256(2)],
            [[uint256(3), uint256(4)], [uint256(5), uint256(6)]],
            [uint256(7), uint256(8)],
            mkLanes(2), mkLanes(4), 5, mkLanes(5),
            keccak256("some later span root")
        );
        assertTrue(settlement.isProvenMessageRoot(root1)); // still queryable

        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l1;
        proof[1] = hashPair(l2, l3);
        dvn.attestPayload(HEADER, l0, CONF, md(root1, proof, 0));
        assertEq(uln.verifyCount(), 1);
        assertEq(uln.lastPayloadHash(), l0);
    }

    // ------------------------------------------------------------------
    // Reject: THE NOMAD LAW (zero/default root leaves the ULN uncalled)
    // ------------------------------------------------------------------

    function test_Nomad_ZeroRootRejected() public {
        recordMsgRoot(keccak256("a real recorded root")); // registry non-empty
        assertFalse(settlement.isProvenMessageRoot(bytes32(0)));

        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, bytes32(0))
        );
        dvn.attestPayload(HEADER, bytes32(0), CONF, md(bytes32(0), emptyProof(), 0));
        assertEq(uln.verifyCount(), 0); // never attested an unproven message
    }

    /// Even with a well-formed-looking payload, a zero root is rejected before
    /// inclusion is examined (the Nomad slot never "defaults to accept").
    function test_Nomad_ZeroRootRejected_WithNonZeroPayload() public {
        recordMsgRoot(keccak256("a real recorded root"));
        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, bytes32(0))
        );
        dvn.attestPayload(
            HEADER, keccak256("payload"), CONF, md(bytes32(0), emptyProof(), 0)
        );
        assertEq(uln.verifyCount(), 0);
    }

    // ------------------------------------------------------------------
    // Reject: unrecorded (but non-zero) root
    // ------------------------------------------------------------------

    function test_Reject_UnrecordedRoot() public {
        recordMsgRoot(keccak256("recorded root A"));
        bytes32 fakeRoot = keccak256("never recorded root B");
        assertFalse(settlement.isProvenMessageRoot(fakeRoot));

        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, fakeRoot)
        );
        dvn.attestPayload(HEADER, fakeRoot, CONF, md(fakeRoot, emptyProof(), 0));
        assertEq(uln.verifyCount(), 0);
    }

    // ------------------------------------------------------------------
    // Reject: inclusion failures (recorded root, but payload not under it)
    // ------------------------------------------------------------------

    /// Tampered sibling: the sorted-pair fold reconstructs a DIFFERENT root.
    function test_Reject_TamperedProof() public {
        (, bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root = _root4(l0, l1, l2, l3);
        recordMsgRoot(root);

        bytes32[] memory bad = new bytes32[](2);
        bad[0] = l1 ^ bytes32(uint256(1)); // flip a bit of the sibling
        bad[1] = hashPair(l2, l3);
        bytes32 computed = hashPair(hashPair(l0, bad[0]), bad[1]);
        assertTrue(computed != root);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggDVN.InclusionProofFailed.selector, computed, root
            )
        );
        dvn.attestPayload(HEADER, l0, CONF, md(root, bad, 0));
        assertEq(uln.verifyCount(), 0);
    }

    /// A payload not in the tree, with an otherwise-valid-shaped proof.
    function test_Reject_LeafNotUnderRoot() public {
        (, bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root = _root4(l0, l1, l2, l3);
        recordMsgRoot(root);

        bytes32 forged = keccak256("a payload never committed");
        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l1;
        proof[1] = hashPair(l2, l3);
        bytes32 computed = hashPair(hashPair(forged, l1), proof[1]);
        assertTrue(computed != root);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggDVN.InclusionProofFailed.selector, computed, root
            )
        );
        dvn.attestPayload(HEADER, forged, CONF, md(root, proof, 0));
        assertEq(uln.verifyCount(), 0);
    }

    // ------------------------------------------------------------------
    // Reject: fail-closed construction pins
    // ------------------------------------------------------------------

    function test_Reject_CodelessSettlementAtConstruction() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggDVN.SettlementHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggDVN(IDreggSettlement(address(0xBEEF)), uln);
    }

    function test_Reject_CodelessUlnAtConstruction() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggDVN.ReceiveUlnHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggDVN(settlement, IReceiveUln(address(0xBEEF)));
    }
}
