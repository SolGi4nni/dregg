// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggPeerRegistry} from "../contracts/DreggPeerRegistry.sol";
import {IDreggPeerRegistry} from "../contracts/IDreggPeerRegistry.sol";
import {IPeerLightClientVerifier} from "../contracts/IPeerLightClientVerifier.sol";
import {LaneCheckingPeerVerifier, RejectingPeerVerifier} from "./DreggPeerRegistry.t.sol";

/// THE PEER-WRAP ↔ REGISTRY WIRING TEST — proves the gnark peer-wrap's
/// public-input MAPPING (chain/gnark/peer_wrap_circuit.go BindPeerFinalityLanes)
/// lines up EXACTLY with what DreggPeerRegistry.submitPeerFinality assembles and
/// checks. It is the on-chain twin of chain/gnark/peer_wrap_circuit_test.go's
/// TestPeerLaneBind*: the Go test proves the wrap CIRCUIT emits
/// [chainId, height, rootHi, rootLo] from the LC statement; this proves the
/// on-chain contract THREADS those same four lanes into the pairing check and
/// records the root — so a produced LC-STARK → peer-wrap Groth16 verifies at the
/// registry, and a forged/mismatched one is rejected.
///
/// Following the file's own convention (DreggPeerRegistry.t.sol), the pairing
/// SOUNDNESS is the pinned verifier's job; a LaneCheckingPeerVerifier stands in
/// for the REAL Groth16 whose statement binds exactly [chainId, height, rootHi,
/// rootLo] (a wrong lane => wrong MSM => failed pairing on a real proof). The
/// REAL-fixture path (test_RealFixture_*) wires an actual generated peer
/// verifier when the fixture exists; absent it, it SKIPS with the named
/// gnark-build residual.
contract DreggPeerRegistryWrapTest is Test {
    bytes32 constant VK_HASH = keccak256("dregg-peer-lightclient-vk-v1");

    // The DEPLOY-PINNED peer chainId convention baked into each per-chain wrap
    // map (peer_wrap_circuit.go): EIP-155 for the EVM peer, SLIP-44 coin type
    // for the non-EVM peers, a reserved placeholder for Midnight.
    uint256 constant CHAIN_ETH = 1;
    uint256 constant CHAIN_BASE = 8453;
    uint256 constant CHAIN_COSMOS = 118; // SLIP-44 ATOM
    uint256 constant CHAIN_SOLANA = 501; // SLIP-44 SOL
    uint256 constant CHAIN_MIDNIGHT = 2718; // reserved placeholder

    // The BabyBear limb radix the wrap packs root felts with (RootLimbRadixBits).
    uint256 constant ROOT_LIMB_RADIX_BITS = 31;

    // Dummy Groth16 proof words (the lane-checking verifier ignores them; the
    // statement lives entirely in the public inputs).
    function _a() internal pure returns (uint256[2] memory) { return [uint256(1), uint256(2)]; }
    function _b() internal pure returns (uint256[2][2] memory) {
        return [[uint256(3), uint256(4)], [uint256(5), uint256(6)]];
    }
    function _c() internal pure returns (uint256[2] memory) { return [uint256(7), uint256(8)]; }
    function _cm() internal pure returns (uint256[2] memory) { return [uint256(9), uint256(10)]; }
    function _pok() internal pure returns (uint256[2] memory) { return [uint256(11), uint256(12)]; }

    /// The Solidity twin of BindPeerFinalityLanes' radix-2^31 Horner packing of
    /// the LC root felt(s), most-significant limb first — the exact 256-bit root
    /// the wrap 128-bit-splits into (rootHi, rootLo). Each felt is a canonical
    /// BabyBear residue (< 2^31), so `<< 31` never overlaps.
    function _packRoot(uint256[] memory felts) internal pure returns (bytes32) {
        uint256 packed = 0;
        for (uint256 i = 0; i < felts.length; i++) {
            require(felts[i] < (uint256(1) << ROOT_LIMB_RADIX_BITS), "felt not canonical");
            packed = (packed << ROOT_LIMB_RADIX_BITS) | felts[i];
        }
        return bytes32(packed);
    }

    function _one(uint256 v) internal pure returns (uint256[] memory a) {
        a = new uint256[](1);
        a[0] = v;
    }

    // ==================================================================
    // The single-felt anchor slice (the CURRENT LC-AIR resolution): the LC
    // exposes one 31-bit root anchor felt, so the wrap maps rootHi=0,
    // rootLo=anchor, and the registry's splitRoot recomposes it exactly.
    // ==================================================================

    /// For every peer chain, the wrap's [chainId, height, rootHi=0, rootLo=anchor]
    /// verifies at a registry pinned to a lane-checking verifier built from the
    /// SAME split — and records provenPeerRoot.
    function test_WrapMapping_SingleFeltAnchor_PerChain() public {
        uint256[5] memory chains =
            [CHAIN_ETH, CHAIN_BASE, CHAIN_COSMOS, CHAIN_SOLANA, CHAIN_MIDNIGHT];
        uint64[5] memory heights =
            [uint64(21_000_000), 21_000_001, 19_000_000, 250_000_000, 42];
        uint256[5] memory anchors = [
            uint256(123456789),
            uint256(222333444),
            uint256(987654321),
            uint256(555666777),
            uint256(2013265900) // near p-1, still canonical
        ];

        for (uint256 i = 0; i < chains.length; i++) {
            bytes32 root = _packRoot(_one(anchors[i]));
            (uint256 hi, uint256 lo) = _splitViaRegistry(root);
            assertEq(hi, 0, "single 31-bit anchor => rootHi 0");
            assertEq(lo, anchors[i], "rootLo == anchor felt");

            LaneCheckingPeerVerifier lv =
                new LaneCheckingPeerVerifier(chains[i], heights[i], hi, lo);
            DreggPeerRegistry reg = new DreggPeerRegistry(lv, VK_HASH);

            reg.submitPeerFinality(
                chains[i], heights[i], root, _a(), _b(), _c(), _cm(), _pok()
            );
            assertTrue(reg.isProvenPeerRoot(chains[i], root), "root must be recorded");
            assertEq(reg.provenPeerRoot(chains[i], heights[i]), root);
            assertEq(reg.latestPeerRoot(chains[i]), root);
            assertEq(reg.latestPeerHeight(chains[i]), heights[i]);
        }
    }

    /// A proof carrying ETH's lanes is REJECTED when submitted as Base: the
    /// chainId lane the wrap bakes (and the registry threads into lane 0) binds
    /// the proof to one chain.
    function test_WrapMapping_RejectsWrongChainId() public {
        bytes32 root = _packRoot(_one(123456789));
        (uint256 hi, uint256 lo) = _splitViaRegistry(root);
        uint64 h = 21_000_000;

        // Verifier pinned to ETH's lanes.
        LaneCheckingPeerVerifier lv = new LaneCheckingPeerVerifier(CHAIN_ETH, h, hi, lo);
        DreggPeerRegistry reg = new DreggPeerRegistry(lv, VK_HASH);

        // Submitting the same (height, root) under Base => lane 0 mismatch => reject.
        vm.expectRevert(IDreggPeerRegistry.ProofRejected.selector);
        reg.submitPeerFinality(CHAIN_BASE, h, root, _a(), _b(), _c(), _cm(), _pok());
        assertFalse(reg.isProvenPeerRoot(CHAIN_BASE, root));
    }

    /// A proof for the right chain but a DIFFERENT root is rejected (the root
    /// lanes bind the finalized commitment).
    function test_WrapMapping_RejectsForgedRoot() public {
        bytes32 root = _packRoot(_one(123456789));
        (uint256 hi, uint256 lo) = _splitViaRegistry(root);
        uint64 h = 100;

        LaneCheckingPeerVerifier lv = new LaneCheckingPeerVerifier(CHAIN_SOLANA, h, hi, lo);
        DreggPeerRegistry reg = new DreggPeerRegistry(lv, VK_HASH);

        bytes32 forged = _packRoot(_one(987654321));
        vm.expectRevert(IDreggPeerRegistry.ProofRejected.selector);
        reg.submitPeerFinality(CHAIN_SOLANA, h + 1, forged, _a(), _b(), _c(), _cm(), _pok());
    }

    // ==================================================================
    // The full 128-bit split (the FORWARD-COMPATIBLE resolution): when the LC
    // AIR exposes the root as N felts, the wrap packs them past 2^128 and the
    // registry's splitRoot must recompose the SAME (rootHi, rootLo) the wrap
    // 128-bit-split in-circuit. rootHi is nonzero here.
    // ==================================================================

    function test_WrapMapping_MultiFeltRootSplitMatchesRegistry() public {
        // A 6-felt root (6·31 = 186 bits) => rootHi != 0.
        uint256[] memory felts = new uint256[](6);
        felts[0] = 2013265900;
        felts[1] = 1234567;
        felts[2] = 2013265900;
        felts[3] = 7;
        felts[4] = 2013265900;
        felts[5] = 42;
        bytes32 root = _packRoot(felts);

        (uint256 hi, uint256 lo) = _splitViaRegistry(root);
        assertTrue(hi != 0, "multi-felt root must exercise a nonzero rootHi split");
        // The registry recomposes exactly (no truncation) — the invariant the
        // wrap's in-circuit `packed == rootHi*2^128 + rootLo` mirrors.
        assertEq(bytes32((hi << 128) | lo), root);

        uint64 h = 12345;
        LaneCheckingPeerVerifier lv = new LaneCheckingPeerVerifier(CHAIN_MIDNIGHT, h, hi, lo);
        DreggPeerRegistry reg = new DreggPeerRegistry(lv, VK_HASH);
        reg.submitPeerFinality(CHAIN_MIDNIGHT, h, root, _a(), _b(), _c(), _cm(), _pok());
        assertTrue(reg.isProvenPeerRoot(CHAIN_MIDNIGHT, root));
    }

    /// A rejecting verifier (a forged proof) records nothing — end to end.
    function test_WrapMapping_ForgedProofRecordsNothing() public {
        RejectingPeerVerifier rv = new RejectingPeerVerifier();
        DreggPeerRegistry reg = new DreggPeerRegistry(rv, VK_HASH);
        bytes32 root = _packRoot(_one(123456789));
        vm.expectRevert(IDreggPeerRegistry.ProofRejected.selector);
        reg.submitPeerFinality(CHAIN_ETH, 1, root, _a(), _b(), _c(), _cm(), _pok());
        assertFalse(reg.isProvenPeerRoot(CHAIN_ETH, root));
    }

    // ==================================================================
    // THE REAL-FIXTURE PATH (the gnark-build residual, named).
    // ==================================================================

    /// When a REAL peer-wrap Groth16 fixture exists — emitted by the gnark peer
    /// setup+prove over an exported LC shrink proof (the twin of
    /// settlement_snark_test.go) — this validates its 4-lane public statement
    /// shape and that the registry's splitRoot recomposes the fixture root. It
    /// SKIPS with the named residual when the fixture is absent: producing it
    /// needs the LC prove (Rust, off-box) + the dev Groth16 setup; the REAL VK
    /// trusted-setup ceremony on top is the ember-gated DEPLOY residual.
    function test_RealFixture_PeerWrapStatementShape() public {
        string memory path = "test/fixtures/peer_finality_groth16.json";
        if (!vm.exists(path)) {
            vm.skip(true);
            emit log("SKIP: no peer_finality_groth16.json -- the gnark-build residual "
                "(export an LC shrink fixture + run the dev Groth16 setup, the twin of "
                "TestSettlementGroth16EndToEnd). The real VK ceremony is the ember-gated deploy step.");
            return;
        }
        string memory json = vm.readFile(path);
        // The pinned 4-lane vector [chainId, height, rootHi, rootLo].
        uint256[] memory inputs = vm.parseJsonUintArray(json, ".inputs");
        assertEq(inputs.length, 4, "peer statement is exactly 4 lanes");
        uint256 chainId = inputs[0];
        uint64 height = uint64(inputs[1]);
        uint256 hi = inputs[2];
        uint256 lo = inputs[3];
        assertTrue(chainId != 0, "chainId lane nonzero");
        assertTrue(hi < (uint256(1) << 128) && lo < (uint256(1) << 128), "128-bit halves");

        bytes32 root = bytes32((hi << 128) | lo);
        (uint256 rhi, uint256 rlo) = _splitViaRegistry(root);
        assertEq(rhi, hi, "registry splitRoot rootHi matches the fixture lane");
        assertEq(rlo, lo, "registry splitRoot rootLo matches the fixture lane");
    }

    // ------------------------------------------------------------------
    // Helper: reach the registry's `splitRoot` pure function without a live
    // instance-under-test (deploy a throwaway registry with a rejecting mock).
    // ------------------------------------------------------------------
    DreggPeerRegistry internal _splitter;

    function _splitViaRegistry(bytes32 root) internal returns (uint256 hi, uint256 lo) {
        if (address(_splitter) == address(0)) {
            _splitter = new DreggPeerRegistry(new RejectingPeerVerifier(), VK_HASH);
        }
        return _splitter.splitRoot(root);
    }
}
