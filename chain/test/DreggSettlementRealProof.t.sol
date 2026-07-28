// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";
import {Groth16Verifier25Adapter} from "../contracts/Groth16Verifier25Adapter.sol";
import {Verifier as DreggGroth16Verifier25} from "../contracts/DreggGroth16Verifier25.sol";
import {DreggSettlementVK} from "../contracts/DreggSettlementVK.sol";

/// THE REAL-PROOF SETTLEMENT TEST: a REAL Groth16 proof — minted by
/// chain/gnark settlement_snark_test.go over the REAL dregg shrink proof
/// (a 2-turn chain folded to an ir2_leaf_wrap apex, re-proven BN254-native,
/// verified in-circuit by SettlementCircuit) — settles on-chain against the
/// REAL gnark-GENERATED verifier (DreggGroth16Verifier25.sol). No mock
/// anywhere on the accept path.
///
/// ⚠ The VK inside the generated verifier comes from a SINGLE-PARTY DEV
/// trusted setup (see settlement_snark_test.go) — real circuit, real
/// verifier, dev ceremony.
///
/// Fixture: chain/test/fixtures/settlement_groth16.json (regenerate with
///   cd chain/gnark && DREGG_SNARK=1 go test -run TestSettlementGroth16EndToEnd -v).
contract DreggSettlementRealProofTest is Test {
    /// The key-derived VK pin (see DreggSettlementVkPin.t.sol). Was
    /// `keccak256("dregg-settlement-vk-dev-setup")` until 2026-07-28.
    bytes32 constant VK_HASH = DreggSettlementVK.VK_DIGEST;

    DreggSettlement settlement;
    Groth16Verifier25Adapter adapter;
    DreggGroth16Verifier25 verifier;

    uint256[2] a;
    uint256[2][2] b;
    uint256[2] c;
    uint256[2] commitments;
    uint256[2] commitmentPok;
    uint32[8] genesisRoot;
    uint32[8] finalRoot;
    uint32 numTurns;
    uint32[8] chainDigest;
    uint256[25] inputs;

    function setUp() public {
        string memory json = vm.readFile("test/fixtures/settlement_groth16.json");

        string[] memory proofWords = vm.parseJsonStringArray(json, ".proof");
        assertEq(proofWords.length, 8, "proof must be 8 words (Ar, Bs, Krs)");
        a = [vm.parseUint(proofWords[0]), vm.parseUint(proofWords[1])];
        b = [
            [vm.parseUint(proofWords[2]), vm.parseUint(proofWords[3])],
            [vm.parseUint(proofWords[4]), vm.parseUint(proofWords[5])]
        ];
        c = [vm.parseUint(proofWords[6]), vm.parseUint(proofWords[7])];

        string[] memory cm = vm.parseJsonStringArray(json, ".commitments");
        assertEq(cm.length, 2, "expected exactly ONE Pedersen commitment (2 words)");
        commitments = [vm.parseUint(cm[0]), vm.parseUint(cm[1])];
        string[] memory pok = vm.parseJsonStringArray(json, ".commitment_pok");
        assertEq(pok.length, 2);
        commitmentPok = [vm.parseUint(pok[0]), vm.parseUint(pok[1])];

        uint256[] memory g = vm.parseJsonUintArray(json, ".genesis_root");
        uint256[] memory f = vm.parseJsonUintArray(json, ".final_root");
        uint256[] memory d = vm.parseJsonUintArray(json, ".chain_digest");
        numTurns = uint32(vm.parseJsonUint(json, ".num_turns"));
        for (uint256 i = 0; i < 8; i++) {
            genesisRoot[i] = uint32(g[i]);
            finalRoot[i] = uint32(f[i]);
            chainDigest[i] = uint32(d[i]);
        }
        string[] memory ins = vm.parseJsonStringArray(json, ".inputs");
        assertEq(ins.length, 25, "the pinned 25-lane statement");
        for (uint256 i = 0; i < 25; i++) {
            inputs[i] = vm.parseUint(ins[i]);
        }

        verifier = new DreggGroth16Verifier25();
        adapter = new Groth16Verifier25Adapter(address(verifier));
        // The settlement anchors at the proof's OWN genesis root, so the
        // real proof chains from construction exactly like a deployment
        // anchored at the dregg chain's genesis.
        settlement = new DreggSettlement(
            IGroth16Verifier25(address(adapter)), VK_HASH, genesisRoot
        );
    }

    /// The generated verifier accepts the raw real proof directly (reverting
    /// interface — success == no revert).
    function test_GeneratedVerifierAcceptsRealProofRaw() public view {
        verifier.verifyProof(
            [a[0], a[1], b[0][0], b[0][1], b[1][0], b[1][1], c[0], c[1]],
            commitments,
            commitmentPok,
            inputs
        );
    }

    /// THE END-TO-END: the real Groth16 proof settles the real dregg root.
    function test_RealProofSettles() public {
        settlement.settle(
            a, b, c, commitments, commitmentPok,
            genesisRoot, finalRoot, numTurns, chainDigest, bytes32(0)
        );
        assertEq(settlement.provenRoot(), settlement.packLanes(finalRoot));
        assertEq(settlement.provenHeight(), numTurns);
        assertTrue(settlement.isProvenRoot(settlement.packLanes(finalRoot)));
    }

    /// THE DECISIVE CANARY, on-chain edition: the SAME real proof presented
    /// with a final root it does not attest must be REJECTED by the real
    /// pairing check.
    function test_RealProofRejectsWrongFinalRoot() public {
        uint32[8] memory forged = finalRoot;
        forged[0] += 1;
        vm.expectRevert(IDreggSettlement.ProofRejected.selector);
        settlement.settle(
            a, b, c, commitments, commitmentPok,
            genesisRoot, forged, numTurns, chainDigest, bytes32(0)
        );
        // Nothing settled.
        assertEq(settlement.provenHeight(), 0);
    }

    /// A forged genesis lane fails CONTINUITY first (the anchor is pinned at
    /// construction) — and even a settlement re-anchored at the forged
    /// genesis would fail the pairing check.
    function test_RealProofRejectsWrongGenesisRoot() public {
        uint32[8] memory forged = genesisRoot;
        forged[3] += 1;
        vm.expectRevert(); // ContinuityBroken(pinned anchor, forged)
        settlement.settle(
            a, b, c, commitments, commitmentPok,
            forged, finalRoot, numTurns, chainDigest, bytes32(0)
        );

        DreggSettlement reAnchored = new DreggSettlement(
            IGroth16Verifier25(address(adapter)), VK_HASH, forged
        );
        vm.expectRevert(IDreggSettlement.ProofRejected.selector);
        reAnchored.settle(
            a, b, c, commitments, commitmentPok,
            forged, finalRoot, numTurns, chainDigest, bytes32(0)
        );
    }

    /// A tampered proof point must be rejected.
    function test_RealProofRejectsTamperedProofPoint() public {
        uint256[2] memory badA = [a[0] + 1, a[1]];
        vm.expectRevert(IDreggSettlement.ProofRejected.selector);
        settlement.settle(
            badA, b, c, commitments, commitmentPok,
            genesisRoot, finalRoot, numTurns, chainDigest, bytes32(0)
        );
    }

    /// A tampered Pedersen commitment must be rejected.
    function test_RealProofRejectsTamperedCommitment() public {
        uint256[2] memory badCm = [commitments[0] + 1, commitments[1]];
        vm.expectRevert(IDreggSettlement.ProofRejected.selector);
        settlement.settle(
            a, b, c, badCm, commitmentPok,
            genesisRoot, finalRoot, numTurns, chainDigest, bytes32(0)
        );
    }

    /// The fixture's flat 25-lane input vector matches the split lanes in the
    /// pinned order (a drifted exporter dies here, not in a pairing failure).
    function test_FixtureInputOrderIsPinned() public view {
        for (uint256 i = 0; i < 8; i++) {
            assertEq(inputs[i], uint256(genesisRoot[i]));
            assertEq(inputs[8 + i], uint256(finalRoot[i]));
            assertEq(inputs[17 + i], uint256(chainDigest[i]));
        }
        assertEq(inputs[16], uint256(numTurns));
    }
}
