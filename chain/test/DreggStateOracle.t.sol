// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggStateOracle} from "../contracts/DreggStateOracle.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";
import {DreggSettlementVK} from "../contracts/DreggSettlementVK.sol";

/// A verifier that accepts. The state-oracle tests are about what the ORACLE binds,
/// not about the pairing — `DreggSettlementRealProof.t.sol` exercises the real proof.
contract AcceptingVerifier is IGroth16Verifier25 {
    function verifyProof(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[25] calldata
    ) external pure returns (bool) {
        return true;
    }

    function vkDigest() external pure returns (bytes32) {
        return DreggSettlementVK.digest();
    }
}

/// ⚑ **THE ORACLE MUST NOT BE ABLE TO REPORT ANYTHING THE PROOF DID NOT ESTABLISH.**
///
/// Until 2026-07-28 `recordEpoch(stateRoot, height, subRootVec)` wrote four keccak
/// mirror sub-roots and a height straight to storage with only `isProvenRoot(stateRoot)`
/// checked. `proveHolding` / `proveNullifierSpent` / `proveCommitmentExists` then served
/// inclusion proofs against those recorder-supplied roots, so a compromised recorder
/// forged every one of them. Both unbound fields are gone: the height is read from the
/// settlement contract (proof-bound), and the sub-root surface is deleted outright
/// because the 25-lane proof cannot bind it (see the named residual in the contract).
///
/// These tests are driven by a REAL `DreggSettlement`, not a mock that returns whatever
/// the test wants — the point is that the numbers come from the settlement state machine.
contract DreggStateOracleTest is Test {
    DreggSettlement settlement;
    DreggStateOracle oracle;

    uint32[8] GENESIS = [uint32(1), 2, 3, 4, 5, 6, 7, 8];
    uint32[8] SPAN1 = [uint32(11), 12, 13, 14, 15, 16, 17, 18];
    uint32[8] SPAN2 = [uint32(21), 22, 23, 24, 25, 26, 27, 28];

    /// ⚑ WAS `keccak256("test-vk")` until 2026-07-30. That this suite was green
    /// with it is the measurement: the settlement contract took a hash of the
    /// string "test-vk" as its "verifying-key commitment" and never looked at it
    /// again. The constructor now refuses any declaration but the verifier's own
    /// key digest.
    bytes32 constant VK_HASH = DreggSettlementVK.VK_DIGEST;

    function setUp() public {
        AcceptingVerifier v = new AcceptingVerifier();
        settlement = new DreggSettlement(IGroth16Verifier25(address(v)), VK_HASH, GENESIS);
        oracle = new DreggStateOracle(IDreggSettlement(address(settlement)));
    }

    // ─── Height: the field that used to be attested ────────────────────────────

    /// POLE 1 (honest) — an indexed epoch reports the height the SETTLEMENT proved,
    /// and different spans report their own different heights.
    function test_EpochHeightComesFromTheProvenSettlement() public {
        _settle(GENESIS, SPAN1, 5);
        _settle(SPAN1, SPAN2, 9);

        bytes32 r1 = settlement.packLanes(SPAN1);
        bytes32 r2 = settlement.packLanes(SPAN2);

        uint256 i1 = oracle.recordEpoch(r1);
        uint256 i2 = oracle.recordEpoch(r2);

        (bytes32 root1, uint64 h1) = oracle.epochAt(i1);
        (bytes32 root2, uint64 h2) = oracle.epochAt(i2);

        assertEq(root1, r1);
        assertEq(root2, r2);
        // The heights are the accumulated numTurns of the verified settlements —
        // 5, then 5 + 9. Nobody supplied them.
        assertEq(h1, 5, "span 1 height is the proven cumulative height");
        assertEq(h2, 14, "span 2 height accumulates");
        assertTrue(h1 != h2, "distinct spans must not collapse to one height");
        assertEq(settlement.provenHeightOf(r1), 5);
        assertEq(settlement.provenHeightOf(r2), 14);
    }

    /// POLE 2 (forgery) — THE RIGHT REJECTION. A caller cannot state a height: the
    /// argument does not exist. Calling the pre-2026-07-28 three-argument
    /// `recordEpoch(bytes32,uint64,bytes32[4])` — the exact signature that accepted an
    /// arbitrary height and arbitrary sub-roots — now hits no function and no
    /// fallback, so it REVERTS rather than recording a forged epoch.
    function test_ForgedHeightAndSubRootsHaveNoEntryPoint() public {
        _settle(GENESIS, SPAN1, 5);
        bytes32 r1 = settlement.packLanes(SPAN1);

        bytes32[4] memory forgedSubRoots = [
            keccak256("forged.balance.root"),
            keccak256("forged.nullifier.root"),
            keccak256("forged.commitments.root"),
            keccak256("forged.heap.root")
        ];
        (bool ok, ) = address(oracle).call(
            abi.encodeWithSignature(
                "recordEpoch(bytes32,uint64,bytes32[4])", r1, uint64(999999), forgedSubRoots
            )
        );
        assertFalse(ok, "the height+sub-root recording entry point must be gone");

        // ...and the deleted read surface is gone too: every accessor that served a
        // recorder-attested value now reverts, so no consumer can be reading one.
        _assertNoSuchFunction(
            abi.encodeWithSignature(
                "proveHolding(bytes32,address,uint256,uint256,bytes32[])",
                r1, address(0xA11CE), uint256(1_000_000), uint256(0), new bytes32[](0)
            ),
            "proveHolding"
        );
        _assertNoSuchFunction(
            abi.encodeWithSignature(
                "proveNullifierSpent(bytes32,bytes32,uint256,bytes32[])",
                r1, keccak256("n"), uint256(0), new bytes32[](0)
            ),
            "proveNullifierSpent"
        );
        _assertNoSuchFunction(
            abi.encodeWithSignature(
                "proveCommitmentExists(bytes32,bytes32,uint256,bytes32[])",
                r1, keccak256("c"), uint256(0), new bytes32[](0)
            ),
            "proveCommitmentExists"
        );
        _assertNoSuchFunction(
            abi.encodeWithSignature("subRootOf(bytes32,uint8)", r1, uint8(1)), "subRootOf"
        );
        _assertNoSuchFunction(
            abi.encodeWithSignature("subRoots(bytes32)", r1), "subRoots"
        );
        _assertNoSuchFunction(
            abi.encodeWithSignature("epochHeight(bytes32)", r1),
            "epochHeight (superseded by settlement.provenHeightOf)"
        );
        _assertNoSuchFunction(abi.encodeWithSignature("recorder()"), "recorder");
    }

    /// The oracle refuses to index a state dregg never settled — the binding that
    /// was already there, still there, and still the right rejection.
    function test_RecordEpochRejectsUnprovenRoot() public {
        bytes32 bogus = keccak256("never.settled");
        vm.expectRevert(
            abi.encodeWithSelector(DreggStateOracle.StateRootNotProven.selector, bogus)
        );
        oracle.recordEpoch(bogus);
    }

    function test_RecordEpochRejectsZeroRoot() public {
        vm.expectRevert(DreggStateOracle.ZeroStateRoot.selector);
        oracle.recordEpoch(bytes32(0));
    }

    function test_RecordEpochIsAppendOnce() public {
        _settle(GENESIS, SPAN1, 5);
        bytes32 r1 = settlement.packLanes(SPAN1);
        oracle.recordEpoch(r1);
        vm.expectRevert(
            abi.encodeWithSelector(DreggStateOracle.EpochAlreadyRecorded.selector, r1)
        );
        oracle.recordEpoch(r1);
    }

    /// Indexing is permissionless BECAUSE there is nothing to attest. Anyone
    /// appending a proven root produces the same, proof-bound, entry.
    function test_IndexingIsPermissionlessAndCarriesNoAttestation() public {
        _settle(GENESIS, SPAN1, 5);
        bytes32 r1 = settlement.packLanes(SPAN1);

        vm.prank(address(0xBEEF));
        uint256 i = oracle.recordEpoch(r1);

        (, uint64 h) = oracle.epochAt(i);
        assertEq(h, 5, "a stranger's recording still reports the proven height");
        assertTrue(oracle.isIndexed(r1));
        assertEq(oracle.epochCount(), 1);
    }

    /// `isIndexed` must NOT be mistaken for `isProvenRoot`: a proven-but-unindexed
    /// root answers false, so nothing can drift into treating the index as the oracle
    /// of provenness.
    function test_IsIndexedIsNotIsProvenRoot() public {
        _settle(GENESIS, SPAN1, 5);
        bytes32 r1 = settlement.packLanes(SPAN1);
        assertTrue(settlement.isProvenRoot(r1), "proven");
        assertFalse(oracle.isIndexed(r1), "but not yet indexed");
    }

    function test_EpochAtOutOfRangeReverts() public {
        vm.expectRevert(
            abi.encodeWithSelector(DreggStateOracle.EpochIndexOutOfRange.selector, 0, 0)
        );
        oracle.epochAt(0);
    }

    // ─── The settlement-side binding these rest on ──────────────────────────────

    /// `provenHeightOf` fails closed for a root that was never proven — it does not
    /// return 0, which would be indistinguishable from the genesis anchor's height.
    function test_ProvenHeightOfFailsClosedForUnprovenRoot() public {
        bytes32 bogus = keccak256("never.settled");
        vm.expectRevert(
            abi.encodeWithSelector(IDreggSettlement.RootNotProven.selector, bogus)
        );
        settlement.provenHeightOf(bogus);
    }

    function test_GenesisAnchorIsProvenAtHeightZero() public view {
        bytes32 g = settlement.packLanes(GENESIS);
        assertTrue(settlement.isProvenRoot(g));
        assertEq(settlement.provenHeightOf(g), 0, "the anchor is height 0, not absent");
    }

    /// A root that recurs keeps its FIRST proven height, matching the Solana
    /// registry's idempotent marker.
    function test_RecurringRootKeepsItsFirstHeight() public {
        _settle(GENESIS, SPAN1, 5);
        _settle(SPAN1, SPAN2, 9);
        _settle(SPAN2, SPAN1, 3); // a cycle back to SPAN1

        assertEq(
            settlement.provenHeightOf(settlement.packLanes(SPAN1)),
            5,
            "the first height at which SPAN1 was proven stands"
        );
        assertEq(settlement.provenHeight(), 17, "the running height still accumulates");
    }

    // ─── helpers ────────────────────────────────────────────────────────────────

    function _settle(uint32[8] memory from, uint32[8] memory to, uint32 turns) internal {
        uint256[2] memory z2;
        uint256[2][2] memory z22;
        uint32[8] memory digest;
        settlement.settle(z2, z22, z2, z2, z2, from, to, turns, digest, bytes32(0));
    }

    function _assertNoSuchFunction(bytes memory payload, string memory name) internal {
        (bool ok, ) = address(oracle).call(payload);
        assertFalse(ok, string.concat(name, " must no longer exist on the oracle"));
    }
}
