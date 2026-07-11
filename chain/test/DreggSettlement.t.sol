// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";

/// Toggleable mock. In strict mode it also compares the received 25-lane
/// vector against a pre-set expectation, so the accept test pins the exact
/// public-input assembly order (not just "the verifier was consulted").
contract MockGroth16Verifier25 is IGroth16Verifier25 {
    bool public result = true;
    bool public strict;
    uint256[25] public expectedInputs;

    function setResult(bool r) external {
        result = r;
    }

    function expectInputs(uint256[25] calldata e) external {
        expectedInputs = e;
        strict = true;
    }

    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[25] calldata publicInputs
    ) external view returns (bool) {
        if (strict) {
            for (uint256 i = 0; i < 25; i++) {
                if (publicInputs[i] != expectedInputs[i]) return false;
            }
        }
        return result;
    }
}

/// A verifier that always reverts (e.g. a malformed generated verifier).
contract RevertingVerifier25 is IGroth16Verifier25 {
    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[25] calldata
    ) external pure returns (bool) {
        revert("verifier: boom");
    }
}

contract DreggSettlementTest is Test {
    uint32 constant P = 2013265921; // BabyBear prime

    MockGroth16Verifier25 verifier;
    DreggSettlement settlement;
    bytes32 constant VK_HASH = keccak256("dregg-settlement-vk-v1");

    // Re-declared for vm.expectEmit (topic hashes match the interface's).
    event Settled(bytes32 indexed oldRoot, bytes32 indexed newRoot, uint64 height);
    event SettledLanes(
        uint32[8] genesisRoot,
        uint32[8] finalRoot,
        uint32 numTurns,
        uint32[8] chainDigest
    );

    function setUp() public {
        verifier = new MockGroth16Verifier25();
        // Genesis is pinned at construction (mkLanes(1)); the first settle
        // chains from it exactly like every later one.
        settlement = new DreggSettlement(verifier, VK_HASH, mkLanes(1));
    }

    // ------------------------------------------------------------------
    // Helpers
    // ------------------------------------------------------------------

    function mkLanes(uint32 seed) internal pure returns (uint32[8] memory l) {
        for (uint32 i = 0; i < 8; i++) {
            // Distinct, canonical, and distinct ACROSS different seeds.
            l[i] = (seed * 7919 + i * 104729 + 1) % P;
        }
    }

    function pinnedInputs(
        uint32[8] memory g,
        uint32[8] memory f,
        uint32 n,
        uint32[8] memory d
    ) internal pure returns (uint256[25] memory v) {
        for (uint256 i = 0; i < 8; i++) {
            v[i] = g[i];
            v[8 + i] = f[i];
            v[17 + i] = d[i];
        }
        v[16] = n;
    }

    function callSettle(
        uint32[8] memory g,
        uint32[8] memory f,
        uint32 n,
        uint32[8] memory d
    ) internal {
        callSettleMsg(g, f, n, d, bytes32(0));
    }

    function callSettleMsg(
        uint32[8] memory g,
        uint32[8] memory f,
        uint32 n,
        uint32[8] memory d,
        bytes32 msgRoot
    ) internal {
        uint256[2] memory a = [uint256(1), uint256(2)];
        uint256[2][2] memory b = [[uint256(3), uint256(4)], [uint256(5), uint256(6)]];
        uint256[2] memory c = [uint256(7), uint256(8)];
        settlement.settle(a, b, c, g, f, n, d, msgRoot);
    }

    function assertLanesEq(uint32[8] memory got, uint32[8] memory want) internal pure {
        for (uint256 i = 0; i < 8; i++) {
            assertEq(got[i], want[i]);
        }
    }

    // ------------------------------------------------------------------
    // Accept paths
    // ------------------------------------------------------------------

    function test_SettleGenesis_AcceptsAndPinsInputOrder() public {
        uint32[8] memory g = mkLanes(1);
        uint32[8] memory f = mkLanes(2);
        uint32[8] memory d = mkLanes(3);
        uint32 n = 42;

        // Strict mock: the settle only succeeds if the contract assembled
        // the 25-lane vector in EXACTLY the pinned order.
        verifier.expectInputs(pinnedInputs(g, f, n, d));

        vm.expectEmit(true, true, false, true, address(settlement));
        emit Settled(settlement.packLanes(g), settlement.packLanes(f), 42);
        vm.expectEmit(false, false, false, true, address(settlement));
        emit SettledLanes(g, f, n, d);

        callSettle(g, f, n, d);

        assertTrue(settlement.genesisEstablished());
        assertEq(settlement.provenHeight(), 42);
        assertEq(settlement.provenRoot(), settlement.packLanes(f));
        assertEq(settlement.genesisAnchor(), settlement.packLanes(g));
        assertLanesEq(settlement.provenRootLanes(), f);
        assertLanesEq(settlement.genesisAnchorLanes(), g);
        assertEq(settlement.verifyingKeyHash(), VK_HASH);
    }

    function test_SettleChained_AdvancesRootAndHeight() public {
        uint32[8] memory g = mkLanes(1);
        uint32[8] memory f1 = mkLanes(2);
        uint32[8] memory f2 = mkLanes(4);
        callSettle(g, f1, 10, mkLanes(3));

        // Second settle must chain from f1 (the current proven root).
        vm.expectEmit(true, true, false, true, address(settlement));
        emit Settled(settlement.packLanes(f1), settlement.packLanes(f2), 15);
        callSettle(f1, f2, 5, mkLanes(5));

        assertEq(settlement.provenHeight(), 15);
        assertEq(settlement.provenRoot(), settlement.packLanes(f2));
        // Genesis anchor stays the FIRST settle's genesis.
        assertEq(settlement.genesisAnchor(), settlement.packLanes(g));
    }

    function test_ProvenRootIsGenesisBeforeFirstSettle() public view {
        // Genesis pinned at construction: provenRoot == genesisAnchor, height 0.
        assertTrue(settlement.genesisEstablished());
        assertEq(settlement.provenRoot(), settlement.packLanes(mkLanes(1)));
        assertEq(settlement.genesisAnchor(), settlement.packLanes(mkLanes(1)));
        assertEq(settlement.provenHeight(), 0);
    }

    function test_ProvenRootsRegistry_HistoricalAndNomadLaw() public {
        // Genesis is recorded from construction; zero is never a proven root.
        assertTrue(settlement.isProvenRoot(settlement.packLanes(mkLanes(1))));
        assertFalse(settlement.isProvenRoot(bytes32(0))); // THE NOMAD LAW
        assertFalse(settlement.isProvenRoot(settlement.packLanes(mkLanes(2))));

        // After two chained settles, BOTH historical finalRoots stay queryable
        // (a cross-chain verifier checks the root proven at dispatch time).
        uint32[8] memory f1 = mkLanes(2);
        uint32[8] memory f2 = mkLanes(4);
        callSettle(mkLanes(1), f1, 10, mkLanes(3));
        callSettle(f1, f2, 5, mkLanes(5));
        assertTrue(settlement.isProvenRoot(settlement.packLanes(f1)));
        assertTrue(settlement.isProvenRoot(settlement.packLanes(f2)));
        assertTrue(settlement.isProvenRoot(settlement.packLanes(mkLanes(1))));
        assertFalse(settlement.isProvenRoot(settlement.packLanes(mkLanes(9))));
    }

    function test_MessageRootRegistry_RecordedAndNomadLaw() public {
        bytes32 msgRoot = keccak256("outbound-span-1");
        assertFalse(settlement.isProvenMessageRoot(msgRoot));
        assertFalse(settlement.isProvenMessageRoot(bytes32(0))); // THE NOMAD LAW

        uint32[8] memory f1 = mkLanes(2);
        callSettleMsg(mkLanes(1), f1, 10, mkLanes(3), msgRoot);
        assertTrue(settlement.isProvenMessageRoot(msgRoot));
        // A settle recording no message root leaves zero un-proven.
        callSettleMsg(f1, mkLanes(4), 5, mkLanes(5), bytes32(0));
        assertFalse(settlement.isProvenMessageRoot(bytes32(0)));
        assertFalse(settlement.isProvenMessageRoot(keccak256("never-recorded")));
    }

    function test_Reject_NonCanonicalGenesisAtConstruction() public {
        // The genesis anchor is canonicality-checked at deployment, not just in settle().
        uint32[8] memory bad = mkLanes(1);
        bad[0] = P;
        vm.expectRevert(
            abi.encodeWithSelector(IDreggSettlement.NonCanonicalLane.selector, 0, P)
        );
        new DreggSettlement(verifier, VK_HASH, bad);
    }

    // ------------------------------------------------------------------
    // Reject: non-canonical lanes (one probe per section of the vector)
    // ------------------------------------------------------------------

    function test_Reject_NonCanonicalGenesisLane() public {
        uint32[8] memory g = mkLanes(1);
        g[0] = P; // exactly the prime: smallest non-canonical value
        vm.expectRevert(
            abi.encodeWithSelector(IDreggSettlement.NonCanonicalLane.selector, 0, P)
        );
        callSettle(g, mkLanes(2), 1, mkLanes(3));
    }

    function test_Reject_NonCanonicalFinalLane() public {
        uint32[8] memory f = mkLanes(2);
        f[7] = type(uint32).max;
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggSettlement.NonCanonicalLane.selector, 15, type(uint32).max
            )
        );
        callSettle(mkLanes(1), f, 1, mkLanes(3));
    }

    function test_Reject_NonCanonicalNumTurns() public {
        vm.expectRevert(
            abi.encodeWithSelector(IDreggSettlement.NonCanonicalLane.selector, 16, P)
        );
        callSettle(mkLanes(1), mkLanes(2), P, mkLanes(3));
    }

    function test_Reject_NonCanonicalDigestLane() public {
        uint32[8] memory d = mkLanes(3);
        d[3] = P + 100;
        vm.expectRevert(
            abi.encodeWithSelector(IDreggSettlement.NonCanonicalLane.selector, 20, P + 100)
        );
        callSettle(mkLanes(1), mkLanes(2), 1, d);
    }

    // ------------------------------------------------------------------
    // Reject: verifier outcomes
    // ------------------------------------------------------------------

    function test_Reject_VerifierReturnsFalse() public {
        verifier.setResult(false);
        vm.expectRevert(IDreggSettlement.ProofRejected.selector);
        callSettle(mkLanes(1), mkLanes(2), 1, mkLanes(3));
        // Nothing settled: state stays at the pinned genesis, height 0.
        assertEq(settlement.provenHeight(), 0);
        assertEq(settlement.provenRoot(), settlement.packLanes(mkLanes(1)));
    }

    function test_Reject_WrongInputOrderIsCaught() public {
        // Vacuity check on the strict mock + order pin: expect a SCRAMBLED
        // order (digest where final belongs). A contract assembling the
        // pinned order must now be rejected by the strict mock.
        uint32[8] memory g = mkLanes(1);
        uint32[8] memory f = mkLanes(2);
        uint32[8] memory d = mkLanes(3);
        verifier.expectInputs(pinnedInputs(g, d, 7, f)); // f <-> d swapped
        vm.expectRevert(IDreggSettlement.ProofRejected.selector);
        callSettle(g, f, 7, d);
    }

    function test_Reject_RevertingVerifier() public {
        RevertingVerifier25 rv = new RevertingVerifier25();
        DreggSettlement s = new DreggSettlement(rv, VK_HASH, mkLanes(1));
        uint256[2] memory a = [uint256(1), uint256(2)];
        uint256[2][2] memory b = [[uint256(3), uint256(4)], [uint256(5), uint256(6)]];
        uint256[2] memory c = [uint256(7), uint256(8)];
        vm.expectRevert(bytes("verifier: boom"));
        s.settle(a, b, c, mkLanes(1), mkLanes(2), 1, mkLanes(3), bytes32(0));
    }

    // ------------------------------------------------------------------
    // Reject: construction (fail-closed pins)
    // ------------------------------------------------------------------

    function test_Reject_CodelessVerifierAddress() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggSettlement.VerifierHasNoCode.selector, address(0xBEEF)
            )
        );
        new DreggSettlement(IGroth16Verifier25(address(0xBEEF)), VK_HASH, mkLanes(1));
    }

    function test_Reject_ZeroVerifyingKeyHash() public {
        vm.expectRevert(IDreggSettlement.ZeroVerifyingKeyHash.selector);
        new DreggSettlement(verifier, bytes32(0), mkLanes(1));
    }

    // ------------------------------------------------------------------
    // Reject: state machine (continuity + monotone height)
    // ------------------------------------------------------------------

    function test_Reject_ZeroTurns() public {
        vm.expectRevert(IDreggSettlement.ZeroTurns.selector);
        callSettle(mkLanes(1), mkLanes(2), 0, mkLanes(3));
    }

    function test_Reject_ZeroTurnsAfterGenesis() public {
        uint32[8] memory g = mkLanes(1);
        uint32[8] memory f1 = mkLanes(2);
        callSettle(g, f1, 10, mkLanes(3));
        // Height regression analog: a settle that does not strictly advance.
        vm.expectRevert(IDreggSettlement.ZeroTurns.selector);
        callSettle(f1, mkLanes(4), 0, mkLanes(5));
        assertEq(settlement.provenHeight(), 10);
    }

    function test_Reject_GenesisMismatch() public {
        uint32[8] memory g = mkLanes(1);
        uint32[8] memory f1 = mkLanes(2);
        callSettle(g, f1, 10, mkLanes(3));

        // A proof from an unrelated anchor does not chain.
        uint32[8] memory stranger = mkLanes(9);
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggSettlement.ContinuityBroken.selector,
                settlement.packLanes(f1),
                settlement.packLanes(stranger)
            )
        );
        callSettle(stranger, mkLanes(4), 5, mkLanes(5));
        assertEq(settlement.provenRoot(), settlement.packLanes(f1));
        assertEq(settlement.provenHeight(), 10);
    }

    function test_Reject_ReplayAndStaleGenesisAnchor() public {
        uint32[8] memory g = mkLanes(1);
        uint32[8] memory f1 = mkLanes(2);
        uint32[8] memory d = mkLanes(3);
        callSettle(g, f1, 10, d);

        // Replaying the same settle: its genesis (the original anchor) no
        // longer equals the proven root — the Rust continuity rule
        // (proof genesis chains from the CURRENT proven root) rejects it.
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggSettlement.ContinuityBroken.selector,
                settlement.packLanes(f1),
                settlement.packLanes(g)
            )
        );
        callSettle(g, f1, 10, d);
    }
}
