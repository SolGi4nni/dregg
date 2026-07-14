// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";
import {DreggGroth16VerifierUpgradeable} from "../contracts/DreggGroth16VerifierUpgradeable.sol";

/// THE UPGRADEABLE-VK REGISTRY test suite.
///
/// The VK now lives in STORAGE keyed by epoch, so a VK-epoch flip is a
/// transaction (`advanceEpoch`), not a verifier + settlement redeploy. This
/// suite proves, over the REAL settlement Groth16 fixture
/// (chain/test/fixtures/settlement_groth16.json — the same real 2-turn apex
/// proof the generated-verifier suite settles):
///
///   * epoch 0 is seeded BYTE-IDENTICAL to the generated verifier, so the
///     live proof still verifies (drop-in `verifyProof` == current epoch);
///   * `DreggSettlement` wired to the registry settles the real proof;
///   * `advanceEpoch(newVk)` moves the pointer — a proof verifies against the
///     epoch whose VK matches it, and OLD epochs stay verifiable;
///   * an epoch FLIP changes settlement behavior with NO redeploy;
///   * the owner gate is real: an ungated `advanceEpoch` REVERTS;
///   * a wrong-epoch proof REJECTS; a malformed VK REVERTS.
contract DreggVerifierEpochRegistryTest is Test {
    bytes32 constant VK_HASH = keccak256("dregg-settlement-vk-dev-setup");

    DreggGroth16VerifierUpgradeable verifier;

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
        commitments = [vm.parseUint(cm[0]), vm.parseUint(cm[1])];
        string[] memory pok = vm.parseJsonStringArray(json, ".commitment_pok");
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
        for (uint256 i = 0; i < 25; i++) {
            inputs[i] = vm.parseUint(ins[i]);
        }

        verifier = new DreggGroth16VerifierUpgradeable();
    }

    // ── epoch 0 seeded byte-identical: the live proof still verifies ────────

    function test_Epoch0SeededAcceptsRealProofViaCurrentEpoch() public view {
        assertEq(verifier.currentEpoch(), 0);
        assertTrue(verifier.isEpochSet(0));
        assertTrue(
            verifier.verifyProof(a, b, c, commitments, commitmentPok, inputs),
            "seeded epoch-0 VK must accept the real live proof"
        );
    }

    function test_Epoch0AcceptsRealProofViaVerifyAtEpoch() public view {
        assertTrue(
            verifier.verifyProofAtEpoch(0, a, b, c, commitments, commitmentPok, inputs)
        );
    }

    function test_TamperedProofRejects() public view {
        uint256[2] memory badA = [a[0] + 1, a[1]];
        assertFalse(
            verifier.verifyProof(badA, b, c, commitments, commitmentPok, inputs),
            "a tampered proof point must fail the real pairing"
        );
    }

    function test_NonCanonicalPublicInputRejects() public view {
        uint256[25] memory bad = inputs;
        // R (the scalar field order) is out of range — must be rejected, not
        // silently reduced.
        bad[0] = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001;
        assertFalse(verifier.verifyProof(a, b, c, commitments, commitmentPok, bad));
    }

    // ── DreggSettlement wired to the registry (drop-in IGroth16Verifier25) ──

    function test_SettlementWiredToRegistrySettlesRealProof() public {
        DreggSettlement settlement = new DreggSettlement(
            IGroth16Verifier25(address(verifier)), VK_HASH, genesisRoot
        );
        settlement.settle(
            a, b, c, commitments, commitmentPok,
            genesisRoot, finalRoot, numTurns, chainDigest, bytes32(0)
        );
        assertEq(settlement.provenRoot(), settlement.packLanes(finalRoot));
        assertEq(settlement.provenHeight(), numTurns);
        assertTrue(settlement.isProvenRoot(settlement.packLanes(finalRoot)));
    }

    // ── the flagship: an epoch flip changes settlement WITHOUT a redeploy ───

    function test_EpochFlipChangesSettlementWithoutRedeploy() public {
        DreggSettlement settlement = new DreggSettlement(
            IGroth16Verifier25(address(verifier)), VK_HASH, genesisRoot
        );

        // Flip to a NEW epoch whose VK is perturbed — the real proof no longer
        // matches the current VK, so settlement (which targets the current
        // epoch) rejects it. Same verifier address, same settlement address:
        // only a transaction, no redeploy.
        DreggGroth16VerifierUpgradeable.VerifyingKey memory perturbed =
            verifier.getVerifyingKey(0);
        // A well-formed (in-field) but WRONG δ — passes _validate, so the flip
        // is accepted, yet the real proof no longer satisfies e(C, −δ).
        perturbed.deltaNeg.x0 = perturbed.deltaNeg.x0 ^ 1;
        verifier.advanceEpoch(perturbed);
        assertEq(verifier.currentEpoch(), 1);

        vm.expectRevert(IDreggSettlement.ProofRejected.selector);
        settlement.settle(
            a, b, c, commitments, commitmentPok,
            genesisRoot, finalRoot, numTurns, chainDigest, bytes32(0)
        );
        assertEq(settlement.provenHeight(), 0, "nothing settled under the wrong VK");

        // Flip again, this time reinstating a VK that matches the real proof
        // (the byte-identical epoch-0 VK). Now the same settlement — never
        // redeployed — accepts the same real proof.
        DreggGroth16VerifierUpgradeable.VerifyingKey memory good =
            verifier.getVerifyingKey(0);
        verifier.advanceEpoch(good);
        assertEq(verifier.currentEpoch(), 2);

        settlement.settle(
            a, b, c, commitments, commitmentPok,
            genesisRoot, finalRoot, numTurns, chainDigest, bytes32(0)
        );
        assertEq(settlement.provenHeight(), numTurns, "settles after the flip, no redeploy");
    }

    // ── advanceEpoch mechanics + old epochs stay verifiable ─────────────────

    function test_AdvanceEpoch_OldStaysVerifiable_WrongEpochRejects() public {
        // epoch 1: a perturbed VK the real proof does NOT satisfy.
        DreggGroth16VerifierUpgradeable.VerifyingKey memory perturbed =
            verifier.getVerifyingKey(0);
        // well-formed (in-field) but WRONG γ — the real proof fails e(L, −γ)
        perturbed.gammaNeg.x0 = perturbed.gammaNeg.x0 ^ 1;
        verifier.advanceEpoch(perturbed);

        // epoch 2: the byte-identical real VK again (a proof under THIS VK
        // verifies at THIS new epoch).
        verifier.advanceEpoch(verifier.getVerifyingKey(0));
        assertEq(verifier.currentEpoch(), 2);

        // old epoch 0 still verifies (proofs minted under the old VK survive a flip)
        assertTrue(
            verifier.verifyProofAtEpoch(0, a, b, c, commitments, commitmentPok, inputs),
            "epoch 0 must stay verifiable after the pointer advanced"
        );
        // wrong epoch (1, the perturbed VK) REJECTS the real proof
        assertFalse(
            verifier.verifyProofAtEpoch(1, a, b, c, commitments, commitmentPok, inputs),
            "the real proof must NOT verify against a different epoch's VK"
        );
        // a proof under the NEW current epoch's (matching) VK verifies
        assertTrue(
            verifier.verifyProofAtEpoch(2, a, b, c, commitments, commitmentPok, inputs)
        );
        // the current-epoch drop-in follows the pointer (epoch 2)
        assertTrue(verifier.verifyProof(a, b, c, commitments, commitmentPok, inputs));
    }

    function test_UnsetEpochRejects() public view {
        assertFalse(verifier.isEpochSet(7));
        assertFalse(
            verifier.verifyProofAtEpoch(7, a, b, c, commitments, commitmentPok, inputs),
            "an epoch with no VK verifies nothing (fail closed)"
        );
    }

    // ── the owner gate (load-bearing security) ──────────────────────────────

    function test_UngatedAdvanceEpochReverts() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        address mallory = address(0xBAD);
        vm.prank(mallory);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.NotOwner.selector, mallory
            )
        );
        verifier.advanceEpoch(vk);
        // pointer unmoved
        assertEq(verifier.currentEpoch(), 0);
    }

    function test_UngatedSetVerifyingKeyReverts() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        vm.prank(address(0xBAD));
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.NotOwner.selector, address(0xBAD)
            )
        );
        verifier.setVerifyingKey(5, vk);
    }

    function test_OwnerCanTransferAndNewOwnerAdvances() public {
        address gov = address(0x60F);
        verifier.transferOwnership(gov);
        assertEq(verifier.owner(), gov);

        // old owner (this test contract) can no longer advance
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.NotOwner.selector, address(this)
            )
        );
        verifier.advanceEpoch(vk);

        // new owner (the "governance" address, standing in for a timelock) can
        vm.prank(gov);
        verifier.advanceEpoch(vk);
        assertEq(verifier.currentEpoch(), 1);
    }

    // ── malformed VK reverts at set time ────────────────────────────────────

    function test_MalformedVkOutOfFieldReverts() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        // P (the base field order) is not a reduced residue — out of field.
        vk.alpha.x = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47;
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.MalformedVerifyingKey.selector, "alpha"
            )
        );
        verifier.advanceEpoch(vk);
    }

    function test_MalformedVkOffCurveReverts() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        // In field but off the G1 curve (y² != x³ + 3).
        vk.ic[3].y = addmod(vk.ic[3].y, 1, 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.MalformedVerifyingKey.selector, "ic"
            )
        );
        verifier.advanceEpoch(vk);
    }

    function test_CannotOverwriteSetEpoch() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.EpochAlreadySet.selector, uint256(0)
            )
        );
        verifier.setVerifyingKey(0, vk);
    }
}
