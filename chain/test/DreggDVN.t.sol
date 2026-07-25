// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggDVN} from "../contracts/DreggDVN.sol";
import {IReceiveUln} from "../contracts/ILayerZeroDVN.sol";
import {DreggPeerRegistry} from "../contracts/DreggPeerRegistry.sol";
import {IDreggPeerRegistry} from "../contracts/IDreggPeerRegistry.sol";
import {AcceptingPeerVerifier} from "./DreggPeerRegistry.t.sol";

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

/// The DVN now binds a payload to a PROVEN PEER ROOT (the source chain's finalized
/// root, established by verifying its light-client-STARK-Groth16 in
/// `DreggPeerRegistry`) — a REAL, live binding, not the fail-closed
/// `isProvenMessageRoot` stub. Tests submit a genuine peer finality (the accepting
/// peer verifier stands in for the pairing) whose proven root IS the keccak
/// sorted-pair payload-tree root, then attest inclusion under it end-to-end.
contract DreggDVNTest is Test {
    AcceptingPeerVerifier verifier;
    MockReceiveUln uln;
    DreggPeerRegistry peers;
    DreggDVN dvn;

    bytes32 constant VK_HASH = keccak256("dregg-peer-lightclient-vk-v1");
    uint256 constant ETH = 1;
    uint256 constant BASE = 8453;

    bytes constant HEADER = hex"0102030405060708";
    uint64 constant CONF = 15;

    // Re-declared for vm.expectEmit (topic hashes match DreggDVN's).
    event PayloadAttested(
        uint256 indexed srcChainId,
        bytes32 indexed root,
        bytes32 indexed payloadHash,
        uint64 confirmations,
        uint256 leafIndex
    );

    function setUp() public {
        verifier = new AcceptingPeerVerifier();
        uln = new MockReceiveUln();
        peers = new DreggPeerRegistry(verifier, VK_HASH);
        dvn = new DreggDVN(peers, uln);
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    /// Record `root` as a proven finalized root of chain `chainId` at a fresh
    /// height, via a (mock-verified) peer finality proof — the REAL binding surface.
    uint64 private _nextHeight = 100;
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

    /// Mirror of DreggDVN._hashPair (sorted-pair) so tests can BUILD fixtures.
    function hashPair(bytes32 a, bytes32 b) internal pure returns (bytes32) {
        return a < b
            ? keccak256(abi.encodePacked(a, b))
            : keccak256(abi.encodePacked(b, a));
    }

    function md(uint256 chainId, bytes32 root, bytes32[] memory proof, uint256 idx)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encode(chainId, root, proof, idx);
    }

    function emptyProof() internal pure returns (bytes32[] memory) {
        return new bytes32[](0);
    }

    // A canonical 4-leaf sorted-pair keccak tree over four payload hashes.
    function _tree4()
        internal
        pure
        returns (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3)
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

    /// Multi-leaf inclusion under a genuinely-proven peer root: payload l0 with
    /// proof [l1, hashPair(l2,l3)] climbs to the proven root => attest once.
    function test_Accept_MultiLeafInclusion_CallsUlnOnce() public {
        (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root = _root4(l0, l1, l2, l3);
        proveRoot(ETH, root);
        assertTrue(peers.isProvenPeerRoot(ETH, root));

        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l1;
        proof[1] = hashPair(l2, l3);

        vm.expectEmit(true, true, true, true, address(dvn));
        emit PayloadAttested(ETH, root, l0, CONF, 0);

        dvn.attestPayload(HEADER, l0, CONF, md(ETH, root, proof, 0));

        assertEq(uln.verifyCount(), 1);
        assertEq(uln.lastHeaderHash(), keccak256(HEADER));
        assertEq(uln.lastPayloadHash(), l0);
        assertEq(uln.lastConfirmations(), CONF);
    }

    /// A HISTORICAL proven root (height 100) still attests after height 101
    /// supersedes it — the dispatch-time semantics a cross-chain verifier needs.
    function test_Accept_HistoricalRoot() public {
        (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root1 = _root4(l0, l1, l2, l3);
        proveRoot(ETH, root1); // height 100

        // Advance ETH's proven finality to a later height / different root.
        proveRoot(ETH, keccak256("eth root @ 101"));
        assertTrue(peers.isProvenPeerRoot(ETH, root1)); // still queryable

        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l1;
        proof[1] = hashPair(l2, l3);
        dvn.attestPayload(HEADER, l0, CONF, md(ETH, root1, proof, 0));
        assertEq(uln.verifyCount(), 1);
        assertEq(uln.lastPayloadHash(), l0);
    }

    // ------------------------------------------------------------------
    // Reject: THE NOMAD LAW (zero/default root leaves the ULN uncalled)
    // ------------------------------------------------------------------

    function test_Nomad_ZeroRootRejected() public {
        proveRoot(ETH, keccak256("a real proven root")); // registry non-empty
        assertFalse(peers.isProvenPeerRoot(ETH, bytes32(0)));

        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, ETH, bytes32(0))
        );
        dvn.attestPayload(HEADER, bytes32(0), CONF, md(ETH, bytes32(0), emptyProof(), 0));
        assertEq(uln.verifyCount(), 0); // never attested an unproven message
    }

    /// Even with a well-formed-looking payload, a zero root is rejected before
    /// inclusion is examined (the Nomad slot never "defaults to accept").
    function test_Nomad_ZeroRootRejected_WithNonZeroPayload() public {
        proveRoot(ETH, keccak256("a real proven root"));
        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, ETH, bytes32(0))
        );
        dvn.attestPayload(
            HEADER, keccak256("payload"), CONF, md(ETH, bytes32(0), emptyProof(), 0)
        );
        assertEq(uln.verifyCount(), 0);
    }

    // ------------------------------------------------------------------
    // Reject: unproven (but non-zero) root
    // ------------------------------------------------------------------

    function test_Reject_UnprovenRoot() public {
        proveRoot(ETH, keccak256("proven root A"));
        bytes32 fakeRoot = keccak256("never proven root B");
        assertFalse(peers.isProvenPeerRoot(ETH, fakeRoot));

        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, ETH, fakeRoot)
        );
        dvn.attestPayload(HEADER, fakeRoot, CONF, md(ETH, fakeRoot, emptyProof(), 0));
        assertEq(uln.verifyCount(), 0);
    }

    /// A root proven for ETH cannot attest a packet claimed from Base (chain-scoped).
    function test_Reject_WrongSourceChain() public {
        (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root = _root4(l0, l1, l2, l3);
        proveRoot(ETH, root); // proven for ETH only

        bytes32[] memory proof = new bytes32[](2);
        proof[0] = l1;
        proof[1] = hashPair(l2, l3);
        vm.expectRevert(
            abi.encodeWithSelector(DreggDVN.RootNotProven.selector, BASE, root)
        );
        dvn.attestPayload(HEADER, l0, CONF, md(BASE, root, proof, 0));
        assertEq(uln.verifyCount(), 0);
    }

    // ------------------------------------------------------------------
    // Reject: inclusion failures (proven root, but payload not under it)
    // ------------------------------------------------------------------

    /// Tampered sibling: the sorted-pair fold reconstructs a DIFFERENT root.
    function test_Reject_TamperedProof() public {
        (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root = _root4(l0, l1, l2, l3);
        proveRoot(ETH, root);

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
        dvn.attestPayload(HEADER, l0, CONF, md(ETH, root, bad, 0));
        assertEq(uln.verifyCount(), 0);
    }

    /// A payload not in the tree, with an otherwise-valid-shaped proof.
    function test_Reject_LeafNotUnderRoot() public {
        (bytes32 l0, bytes32 l1, bytes32 l2, bytes32 l3) = _tree4();
        bytes32 root = _root4(l0, l1, l2, l3);
        proveRoot(ETH, root);

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
        dvn.attestPayload(HEADER, forged, CONF, md(ETH, root, proof, 0));
        assertEq(uln.verifyCount(), 0);
    }

    // ------------------------------------------------------------------
    // Reject: fail-closed construction pins
    // ------------------------------------------------------------------

    function test_Reject_CodelessRegistryAtConstruction() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggDVN.PeerRegistryHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggDVN(IDreggPeerRegistry(address(0xBEEF)), uln);
    }

    function test_Reject_CodelessUlnAtConstruction() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggDVN.ReceiveUlnHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggDVN(peers, IReceiveUln(address(0xBEEF)));
    }
}
