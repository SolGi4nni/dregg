// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggVerifier, IDreggVerifier, DreggAttestation} from "../contracts/socket/DreggVerifier.sol";
import {TrustsADreggClearing} from "../contracts/socket/TrustsADreggClearing.sol";
import {DreggGroth16VerifierUpgradeable} from "../contracts/DreggGroth16VerifierUpgradeable.sol";
import {IGroth16VerifierRegistry} from "../contracts/IGroth16VerifierRegistry.sol";

/// THE OCIP SECURITY-PROVIDER SOCKET test — "an external contract consumes a
/// DREGG attestation," end-to-end on-chain, both polarities.
///
/// Stack, exactly as a third party would wire it:
///   DreggGroth16VerifierUpgradeable (the VK-epoch registry, epoch 0 seeded with
///     the LIVE dev-ceremony VK)                                          ← existing
///   → DreggVerifier (the socket; wraps the registry, absorbs VK rotation) ← new
///   → TrustsADreggClearing (a DEMO external consumer; gates a trade on the
///     attestation)                                                        ← new
///
/// The proof is the REAL 2-turn wrap fixture
/// (chain/test/fixtures/settlement_groth16.json — the same fresh proof the
/// Base 7/7, Solana 2/2, Cosmos 5/5 suites verify in
/// docs/deos/CROSS-CHAIN-SETTLEMENT-REALNESS.md). No mock on the accept path.
///
/// ⚠ dev-ceremony: the registry's epoch-0 VK is a single-party dev setup — this
/// is a DEMO OF THE INTERFACE, not production trust (OCIP-SECURITY-SOCKET.md).
contract DreggSocketTest is Test {
    DreggGroth16VerifierUpgradeable registry;
    DreggVerifier socket;
    TrustsADreggClearing consumer;

    // Real proof fixture, split into the socket's typed Proof + Statement.
    DreggAttestation.Proof proof;
    DreggAttestation.Statement stmt;
    uint256[25] rawInputs;

    function setUp() public {
        string memory json = vm.readFile("test/fixtures/settlement_groth16.json");

        string[] memory proofWords = vm.parseJsonStringArray(json, ".proof");
        assertEq(proofWords.length, 8, "proof must be 8 words (Ar, Bs, Krs)");
        proof.a = [vm.parseUint(proofWords[0]), vm.parseUint(proofWords[1])];
        proof.b = [
            [vm.parseUint(proofWords[2]), vm.parseUint(proofWords[3])],
            [vm.parseUint(proofWords[4]), vm.parseUint(proofWords[5])]
        ];
        proof.c = [vm.parseUint(proofWords[6]), vm.parseUint(proofWords[7])];

        string[] memory cm = vm.parseJsonStringArray(json, ".commitments");
        proof.commitments = [vm.parseUint(cm[0]), vm.parseUint(cm[1])];
        string[] memory pok = vm.parseJsonStringArray(json, ".commitment_pok");
        proof.commitmentPok = [vm.parseUint(pok[0]), vm.parseUint(pok[1])];

        uint256[] memory g = vm.parseJsonUintArray(json, ".genesis_root");
        uint256[] memory f = vm.parseJsonUintArray(json, ".final_root");
        uint256[] memory d = vm.parseJsonUintArray(json, ".chain_digest");
        stmt.numTurns = uint32(vm.parseJsonUint(json, ".num_turns"));
        for (uint256 i = 0; i < 8; i++) {
            stmt.genesisRoot[i] = uint32(g[i]);
            stmt.finalRoot[i] = uint32(f[i]);
            stmt.chainDigest[i] = uint32(d[i]);
        }
        string[] memory ins = vm.parseJsonStringArray(json, ".inputs");
        assertEq(ins.length, 25, "the pinned 25-lane statement");
        for (uint256 i = 0; i < 25; i++) {
            rawInputs[i] = vm.parseUint(ins[i]);
        }

        registry = new DreggGroth16VerifierUpgradeable();
        socket = new DreggVerifier(IGroth16VerifierRegistry(address(registry)));
        // The external consumer trusts the dregg instance whose genesis anchor
        // is the fixture's genesis root.
        consumer = new TrustsADreggClearing(IDreggVerifier(address(socket)), stmt.genesisRoot);
    }

    // ── the socket itself ───────────────────────────────────────────────────

    function test_SocketWrapsRegistry() public view {
        assertEq(address(socket.registry()), address(registry));
        assertEq(socket.currentEpoch(), 0);
    }

    function test_SocketRejectsCodelessRegistry() public {
        vm.expectRevert(
            abi.encodeWithSelector(DreggVerifier.RegistryHasNoCode.selector, address(0xdead))
        );
        new DreggVerifier(IGroth16VerifierRegistry(address(0xdead)));
    }

    /// The socket verifies the REAL proof (raw 25-lane form + typed form agree).
    function test_SocketVerifiesRealAttestation() public view {
        assertTrue(socket.verifyDreggAttestation(proof, rawInputs));
        assertTrue(socket.verifyStatement(proof, stmt));
    }

    /// The socket REJECTS a tampered proof (fail-closed bool, no revert).
    function test_SocketRejectsForgedAttestation() public view {
        DreggAttestation.Proof memory bad = proof;
        bad.a[0] = bad.a[0] + 1;
        assertFalse(socket.verifyStatement(bad, stmt));
    }

    /// A non-canonical statement lane is ILL-FORMED (not a forgery) → revert.
    function test_SocketRevertsNonCanonicalLane() public {
        DreggAttestation.Statement memory badStmt = stmt;
        badStmt.finalRoot[0] = 2013265921; // == BABYBEAR_P, out of field
        vm.expectRevert(
            abi.encodeWithSelector(DreggAttestation.NonCanonicalLane.selector, uint256(8), uint32(2013265921))
        );
        socket.verifyStatement(proof, badStmt);
    }

    // ── the external consumer (the security-provider model) ─────────────────

    /// POLARITY 1 — VALID proof: the external contract ACCEPTS the DREGG-attested
    /// clearing and then lets a trade settle against it.
    function test_ConsumerAcceptsValidClearing() public {
        assertEq(consumer.clearingsAccepted(), 0);

        bytes32 finalRoot = consumer.acceptClearing(proof, stmt);

        assertEq(consumer.clearingsAccepted(), 1);
        assertTrue(consumer.acceptedClearing(finalRoot));
        assertEq(consumer.latestTrustedRoot(), finalRoot);
        assertEq(finalRoot, DreggAttestation.packLanes(stmt.finalRoot));

        // The gated economic action now works — but only against the attested root.
        consumer.settleTrade(finalRoot, 1000);
    }

    /// POLARITY 2 — FORGED proof: the external contract REJECTS. A tampered
    /// proof point makes the real BN254 pairing fail, the socket returns false,
    /// and the consumer refuses the clearing. Nothing is recorded.
    function test_ConsumerRejectsForgedClearing() public {
        DreggAttestation.Proof memory bad = proof;
        bad.a[0] = bad.a[0] + 1;

        vm.expectRevert(TrustsADreggClearing.AttestationRejected.selector);
        consumer.acceptClearing(bad, stmt);

        assertEq(consumer.clearingsAccepted(), 0);
        assertFalse(consumer.acceptedClearing(DreggAttestation.packLanes(stmt.finalRoot)));
    }

    /// FORGED via a lied-about final root: the same real proof presented with a
    /// final root it does not attest → pairing fails → consumer rejects.
    function test_ConsumerRejectsWrongFinalRoot() public {
        DreggAttestation.Statement memory forged = stmt;
        forged.finalRoot[0] = forged.finalRoot[0] + 1;

        vm.expectRevert(TrustsADreggClearing.AttestationRejected.selector);
        consumer.acceptClearing(proof, forged);
        assertEq(consumer.clearingsAccepted(), 0);
    }

    /// A valid proof about a DIFFERENT dregg instance is refused BEFORE the
    /// pairing: the consumer trusts exactly one genesis anchor.
    function test_ConsumerRejectsUntrustedDreggInstance() public {
        DreggAttestation.Statement memory foreign = stmt;
        foreign.genesisRoot[0] = foreign.genesisRoot[0] + 1;

        vm.expectRevert(
            abi.encodeWithSelector(
                TrustsADreggClearing.UntrustedDreggInstance.selector,
                DreggAttestation.packLanes(foreign.genesisRoot),
                DreggAttestation.packLanes(stmt.genesisRoot)
            )
        );
        consumer.acceptClearing(proof, foreign);
    }

    /// The gated action is genuinely gated: a trade against a never-attested
    /// root reverts.
    function test_SettleTradeRejectsUnattestedRoot() public {
        bytes32 phantom = keccak256("never attested");
        vm.expectRevert(
            abi.encodeWithSelector(TrustsADreggClearing.NoTrustedClearing.selector, phantom)
        );
        consumer.settleTrade(phantom, 1);
    }

    // ── VK rotation is absorbed by the socket ───────────────────────────────

    /// After the registry advances to a NEW epoch whose VK does NOT match the
    /// proof, the SAME consumer (unchanged, no redeploy) now rejects — the
    /// socket always checks the current epoch. This is the rotation-absorbing
    /// property: the consumer reacts to nothing; the registry owner rotates.
    function test_SocketAbsorbsVkRotation() public {
        // Valid under epoch 0.
        assertTrue(socket.verifyStatement(proof, stmt));

        // Advance to epoch 1 with a DIFFERENT (well-formed but non-matching) VK:
        // reuse epoch 0's VK with alpha replaced by a valid on-curve point that
        // is not the real alpha, so the proof no longer verifies.
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = registry.getVerifyingKey(0);
        // (1, 2) is the BN254 G1 generator — on-curve, in-field, != real alpha.
        vk.alpha.x = 1;
        vk.alpha.y = 2;
        registry.advanceEpoch(vk);
        assertEq(socket.currentEpoch(), 1);

        // The consumer, untouched, now rejects against the current epoch.
        vm.expectRevert(TrustsADreggClearing.AttestationRejected.selector);
        consumer.acceptClearing(proof, stmt);

        // But the proof is STILL verifiable at its original epoch 0 via the
        // socket's epoch-targeted path (old proofs stay valid at their epoch).
        assertTrue(socket.verifyStatementAtEpoch(0, proof, stmt));
        assertFalse(socket.verifyStatementAtEpoch(1, proof, stmt));
    }
}
