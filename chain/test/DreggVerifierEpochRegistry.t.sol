// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";
import {DreggGroth16VerifierUpgradeable} from "../contracts/DreggGroth16VerifierUpgradeable.sol";
import {DreggSettlementVK} from "../contracts/DreggSettlementVK.sol";

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
///   * a timelocked `proposeEpoch(newVk)` → `activateEpoch` flip moves the
///     pointer — a proof verifies against the epoch whose VK matches it, and
///     OLD epochs stay verifiable;
///   * an epoch FLIP changes settlement behavior with NO redeploy;
///   * the owner gate is real: an ungated propose/activate REVERTS;
///   * the TIMELOCK is real: activating before the delay elapses REVERTS, and
///     the staged VK is inert until activation;
///   * a wrong-epoch proof REJECTS; a malformed VK REVERTS at propose time.
contract DreggVerifierEpochRegistryTest is Test {
    /// The key-derived VK pin (see DreggSettlementVkPin.t.sol). Was
    /// `keccak256("dregg-settlement-vk-dev-setup")` until 2026-07-28.
    bytes32 constant VK_HASH = DreggSettlementVK.VK_DIGEST;

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

    /// Drive the two-phase timelocked flip as owner: propose, wait out the
    /// mandatory delay, activate. This is now the ONLY way the pointer moves.
    function _flip(DreggGroth16VerifierUpgradeable.VerifyingKey memory vk) internal {
        verifier.proposeEpoch(vk);
        vm.warp(block.timestamp + verifier.TIMELOCK_DELAY() + 1);
        verifier.activateEpoch();
    }

    // ══════════════════════════════════════════════════════════════════
    // ⚑ THE VK COMMITMENT, COMPUTED FROM STORAGE.
    //
    // This registry is the one place on the EVM where the pin is fully
    // self-evidencing: the key lives in STORAGE, so `vkDigestAtEpoch` hashes
    // the very words `_verify` feeds the precompile. There is no second copy to
    // drift, and no off-chain gate standing in for the relation.
    //
    // The property the superseded pin could not have: TWO DIFFERENT KEYS MUST
    // PRODUCE TWO DIFFERENT COMMITMENTS. `keccak256("dregg-settlement-vk-dev-
    // setup")` produced ONE commitment for every key that will ever exist.
    // ══════════════════════════════════════════════════════════════════

    /// The digest computed from the registry's STORED epoch-0 key equals the
    /// generated constant every chain pins — an ON-CHAIN cross-check between
    /// the storage key and `DreggSettlementVK`'s copy of the same key, and
    /// therefore also against Solana's and Cosmos's emitted `VK_DIGEST`.
    function test_StorageDerivedDigestEqualsTheCrossChainConstant() public view {
        assertEq(
            verifier.vkDigestAtEpoch(0),
            DreggSettlementVK.VK_DIGEST,
            "the stored epoch-0 key must digest to the generated constant"
        );
        assertEq(
            verifier.vkDigest(),
            DreggSettlementVK.VK_DIGEST,
            "vkDigest() tracks the current epoch"
        );
        assertEq(
            verifier.vkDigest(),
            0xcfda612f472e998d1f1bad1bf545ec5b39ca99b64db94e46edf2e8d3790a37cc,
            "byte-identical to solana vk::VK_DIGEST and cosmos vk::VK_DIGEST"
        );
    }

    /// An UNSET epoch has no commitment. Fail-closed: reporting the all-zero
    /// key's digest for an epoch that was never written would be a Nomad-law
    /// default masquerading as a commitment.
    function test_UnsetEpochHasNoDigest() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.MalformedVerifyingKey.selector,
                "epoch not set"
            )
        );
        verifier.vkDigestAtEpoch(1);
    }

    /// ⚑ THE FIRST POLE, AND THE ONE THAT MATTERS: 47 genuinely DIFFERENT
    /// verifying keys, each really installed in storage by a timelocked epoch
    /// flip, produce 47 PAIRWISE-DISTINCT commitments — plus epoch 0 = 48.
    ///
    /// The old label hash scores 0 of 47 here BY CONSTRUCTION: it never reads
    /// the key, so all 48 of its values are the same 32 bytes
    /// (`test_TheOldLabelPinDetectsNoneOfThem` below).
    ///
    /// The perturbations are the ones `_validate` admits, which is the honest
    /// set — a G2 coordinate bit-flip (in-field is all that is checked there),
    /// and G1 TRANSPOSITIONS (swapping two on-curve points stays on-curve).
    /// A transposed IC vector is exactly the kind of ceremony-output slip a VK
    /// commitment exists to catch, and it is invisible to a length or a
    /// well-formedness check.
    function test_FortySevenDifferentKeysGiveFortySevenDifferentDigests() public {
        bytes32[48] memory seen;
        uint256 n = 0;
        seen[n++] = verifier.vkDigestAtEpoch(0);

        // (a) every one of the 20 G2 coordinate words, bit-flipped.
        for (uint256 i = 0; i < 20; i++) {
            DreggGroth16VerifierUpgradeable.VerifyingKey memory k =
                verifier.getVerifyingKey(0);
            _perturbG2Word(k, i);
            _flip(k);
            seen[n++] = verifier.vkDigest();
        }

        // (b) 26 IC transpositions ic[i] <-> ic[i+1]: a different key, every
        //     point still on-curve, same multiset of points.
        for (uint256 i = 0; i < 26; i++) {
            DreggGroth16VerifierUpgradeable.VerifyingKey memory k =
                verifier.getVerifyingKey(0);
            (k.ic[i], k.ic[i + 1]) = (k.ic[i + 1], k.ic[i]);
            _flip(k);
            seen[n++] = verifier.vkDigest();
        }

        // (c) alpha <-> ic[0]: both G1, both on-curve, a different key.
        {
            DreggGroth16VerifierUpgradeable.VerifyingKey memory k =
                verifier.getVerifyingKey(0);
            (k.alpha, k.ic[0]) = (k.ic[0], k.alpha);
            _flip(k);
            seen[n++] = verifier.vkDigest();
        }

        assertEq(n, 48, "epoch 0 plus 47 distinct installed keys");
        for (uint256 i = 0; i < n; i++) {
            for (uint256 j = i + 1; j < n; j++) {
                assertTrue(
                    seen[i] != seen[j],
                    "two different verifying keys produced the same commitment"
                );
            }
        }
    }

    /// The defect, as a passing measurement. Across the same key changes the
    /// superseded pin is CONSTANT — it detects 0 of them, because the preimage
    /// contains zero VK bytes.
    function test_TheOldLabelPinDetectsNoneOfThem() public {
        bytes32 label = keccak256("dregg-settlement-vk-dev-setup");
        assertEq(
            label,
            0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76,
            "the superseded pin, recorded"
        );
        bytes32 before = verifier.vkDigest();
        for (uint256 i = 0; i < 6; i++) {
            DreggGroth16VerifierUpgradeable.VerifyingKey memory k =
                verifier.getVerifyingKey(0);
            _perturbG2Word(k, i);
            _flip(k);
            assertTrue(verifier.vkDigest() != before, "the key-derived pin moved");
            assertEq(
                keccak256("dregg-settlement-vk-dev-setup"),
                label,
                "...and the label hash did not, and never could"
            );
        }
        assertTrue(label != DreggSettlementVK.VK_DIGEST);
    }

    /// A settlement wired to the registry reports the CURRENT epoch's key
    /// digest — it follows a flip instead of reporting a stale constructor
    /// argument. (`_verifyingKeyHash` storage is gone for exactly this reason.)
    function test_SettlementPinFollowsTheEpochFlip() public {
        DreggSettlement settlement = new DreggSettlement(
            IGroth16Verifier25(address(verifier)), VK_HASH, genesisRoot
        );
        assertEq(settlement.verifyingKeyHash(), DreggSettlementVK.VK_DIGEST);

        DreggGroth16VerifierUpgradeable.VerifyingKey memory k =
            verifier.getVerifyingKey(0);
        k.deltaNeg.x0 = k.deltaNeg.x0 ^ 1;
        _flip(k);

        assertEq(
            settlement.verifyingKeyHash(),
            verifier.vkDigest(),
            "the settlement's pin must be the key that now verifies"
        );
        assertTrue(
            settlement.verifyingKeyHash() != DreggSettlementVK.VK_DIGEST,
            "and must NOT still report the key it was deployed against"
        );
    }

    /// Deploying against the registry with a pin that is not the current
    /// epoch's key digest is REFUSED.
    function test_SettlementRefusesAPinThatIsNotTheRegistrysKey() public {
        vm.expectRevert(
            abi.encodeWithSelector(
                IDreggSettlement.VerifyingKeyHashMismatch.selector,
                DreggSettlementVK.VK_DIGEST,
                keccak256("dregg-settlement-vk-dev-setup")
            )
        );
        new DreggSettlement(
            IGroth16Verifier25(address(verifier)),
            keccak256("dregg-settlement-vk-dev-setup"),
            genesisRoot
        );
    }

    /// Bit-flip G2 coordinate word `i` of the key, in the digest's pinned order
    /// (betaNeg, gammaNeg, deltaNeg, pedersenG, pedersenGSigma; x1,x0,y1,y0).
    /// A flipped low bit stays a reduced Fp residue, which is all `_validate`
    /// checks for G2 — so the flip really installs.
    function _perturbG2Word(
        DreggGroth16VerifierUpgradeable.VerifyingKey memory k,
        uint256 i
    ) internal pure {
        uint256 which = i / 4;
        uint256 word = i % 4;
        if (which == 0) _bump(k.betaNeg, word);
        else if (which == 1) _bump(k.gammaNeg, word);
        else if (which == 2) _bump(k.deltaNeg, word);
        else if (which == 3) _bump(k.pedersenG, word);
        else _bump(k.pedersenGSigma, word);
    }

    function _bump(DreggGroth16VerifierUpgradeable.G2Point memory p, uint256 word)
        internal
        pure
    {
        if (word == 0) p.x1 = p.x1 ^ 1;
        else if (word == 1) p.x0 = p.x0 ^ 1;
        else if (word == 2) p.y1 = p.y1 ^ 1;
        else p.y0 = p.y0 ^ 1;
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
        _flip(perturbed);
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
        _flip(good);
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
        _flip(perturbed);

        // epoch 2: the byte-identical real VK again (a proof under THIS VK
        // verifies at THIS new epoch).
        _flip(verifier.getVerifyingKey(0));
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

    function test_UngatedProposeEpochReverts() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        address mallory = address(0xBAD);
        vm.prank(mallory);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.NotOwner.selector, mallory
            )
        );
        verifier.proposeEpoch(vk);
        // pointer unmoved, nothing pending
        assertEq(verifier.currentEpoch(), 0);
    }

    function test_UngatedActivateEpochReverts() public {
        // Owner stages a legit proposal…
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        verifier.proposeEpoch(vk);
        vm.warp(block.timestamp + verifier.TIMELOCK_DELAY() + 1);
        // …but a non-owner cannot activate it.
        vm.prank(address(0xBAD));
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.NotOwner.selector, address(0xBAD)
            )
        );
        verifier.activateEpoch();
        assertEq(verifier.currentEpoch(), 0);
    }

    // ── the TIMELOCK (the load-bearing #1 fix) ──────────────────────────────

    function test_ActivateBeforeDelayReverts() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        (, uint256 eta) = verifier.proposeEpoch(vk);
        // The VK is staged but INERT: current epoch unmoved, epoch 1 not yet set.
        assertEq(verifier.currentEpoch(), 0);
        assertFalse(verifier.isEpochSet(1));
        // Activating before the timelock elapses REVERTS.
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.ProposalNotReady.selector, eta
            )
        );
        verifier.activateEpoch();
        // One second before eta still reverts.
        vm.warp(eta - 1);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.ProposalNotReady.selector, eta
            )
        );
        verifier.activateEpoch();
        assertEq(verifier.currentEpoch(), 0);
    }

    function test_ActivateAfterDelaySucceeds() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        (uint256 epoch, uint256 eta) = verifier.proposeEpoch(vk);
        assertEq(epoch, 1);
        vm.warp(eta); // exactly eta is enough (>= eta)
        uint256 activated = verifier.activateEpoch();
        assertEq(activated, 1);
        assertEq(verifier.currentEpoch(), 1);
        // The flipped-in VK (byte-identical to epoch 0) verifies the real proof.
        assertTrue(verifier.verifyProof(a, b, c, commitments, commitmentPok, inputs));
    }

    function test_StagedVkIsInertDuringTimelock() public {
        // Propose a perturbed VK the real proof does NOT satisfy.
        DreggGroth16VerifierUpgradeable.VerifyingKey memory perturbed = verifier.getVerifyingKey(0);
        perturbed.deltaNeg.x0 = perturbed.deltaNeg.x0 ^ 1;
        verifier.proposeEpoch(perturbed);
        // During the timelock the CURRENT epoch (0) is untouched — the live proof
        // still verifies, and the staged epoch 1 is not yet verifiable.
        assertTrue(verifier.verifyProof(a, b, c, commitments, commitmentPok, inputs));
        assertFalse(verifier.isEpochSet(1));
        assertFalse(verifier.verifyProofAtEpoch(1, a, b, c, commitments, commitmentPok, inputs));
    }

    function test_CancelProposalVetoesTheFlip() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        verifier.proposeEpoch(vk);
        verifier.cancelProposal();
        // Nothing to activate after a veto — even after the delay.
        vm.warp(block.timestamp + verifier.TIMELOCK_DELAY() + 1);
        vm.expectRevert(DreggGroth16VerifierUpgradeable.NoPendingProposal.selector);
        verifier.activateEpoch();
        assertEq(verifier.currentEpoch(), 0);
    }

    // ── two-step ownership ──────────────────────────────────────────────────

    function test_TwoStepOwnershipTransfer() public {
        address gov = address(0x60F);
        // Step 1: nominate. Ownership does NOT move yet.
        verifier.transferOwnership(gov);
        assertEq(verifier.owner(), address(this));
        assertEq(verifier.pendingOwner(), gov);

        // A non-nominee cannot accept.
        vm.prank(address(0xBAD));
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.NotPendingOwner.selector, address(0xBAD)
            )
        );
        verifier.acceptOwnership();

        // Step 2: the nominee accepts — now ownership moves.
        vm.prank(gov);
        verifier.acceptOwnership();
        assertEq(verifier.owner(), gov);
        assertEq(verifier.pendingOwner(), address(0));

        // The old owner can no longer propose; the new owner can drive a flip.
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.NotOwner.selector, address(this)
            )
        );
        verifier.proposeEpoch(vk);

        vm.startPrank(gov);
        verifier.proposeEpoch(vk);
        vm.warp(block.timestamp + verifier.TIMELOCK_DELAY() + 1);
        verifier.activateEpoch();
        vm.stopPrank();
        assertEq(verifier.currentEpoch(), 1);
    }

    // ── malformed VK reverts at PROPOSE time ────────────────────────────────

    function test_MalformedVkOutOfFieldReverts() public {
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        // P (the base field order) is not a reduced residue — out of field.
        vk.alpha.x = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47;
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggGroth16VerifierUpgradeable.MalformedVerifyingKey.selector, "alpha"
            )
        );
        verifier.proposeEpoch(vk);
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
        verifier.proposeEpoch(vk);
    }

    function test_CannotProposeOverAnAlreadySetEpoch() public {
        // Land epoch 1 through the timelock…
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = verifier.getVerifyingKey(0);
        _flip(vk);
        assertEq(verifier.currentEpoch(), 1);
        // …then activate epoch 2 as well, so both 1 and 2 are set.
        _flip(vk);
        assertEq(verifier.currentEpoch(), 2);
        // A fresh proposal always targets currentEpoch+1 (3, unset) — set epochs
        // can never be overwritten. Sanity: the pointer only ever moves forward.
        assertTrue(verifier.isEpochSet(1));
        assertTrue(verifier.isEpochSet(2));
        assertFalse(verifier.isEpochSet(3));
    }
}
