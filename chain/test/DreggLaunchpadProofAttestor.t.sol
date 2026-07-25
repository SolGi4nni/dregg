// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";
import {DreggProofAttestor} from "../contracts/launchpad/DreggProofAttestor.sol";
import {IDeployerGate} from "../contracts/launchpad/IDeployerGate.sol";
import {DreggVerifier, IDreggVerifier, DreggAttestation} from "../contracts/socket/DreggVerifier.sol";
import {DreggGroth16VerifierUpgradeable} from "../contracts/DreggGroth16VerifierUpgradeable.sol";
import {IGroth16VerifierRegistry} from "../contracts/IGroth16VerifierRegistry.sol";

/// THE PROVED RUNG, WIRED — a launch's clearing gated on a REAL dregg
/// Groth16(BN254) proof verified on-chain through the OCIP socket, with no
/// committee anywhere in the loop.
///
/// The stack under test is the real one, end to end:
///   DreggGroth16VerifierUpgradeable (VK-epoch registry, epoch 0 = the live
///     dev-ceremony VK)                                            ← existing
///   → DreggVerifier (the OCIP socket; real BN254 pairing)         ← existing
///   → DreggProofAttestor (IClearingAttestor, proof arm)           ← new
///   → DreggLaunchpad.finalizeClearing                             ← existing
///
/// The proof is the REAL 2-turn wrap fixture
/// (`test/fixtures/settlement_groth16.json`) — the same proof `DreggSocket.t.sol`
/// and `DreggSettlementRealProof.t.sol` verify. No mock on the accept path.
///
/// ⚑ WHAT IS AND IS NOT PROVED HERE (see `DreggProofAttestor.sol` §Trust):
/// the proof attests a CONSERVED DREGG STATE TRANSITION on the pinned instance —
/// the 25 lanes carry no clearing price and no book, so they cannot and do not
/// attest "this transition was launch #7's clearing." That link is the BINDER's
/// trusted assertion. The clearing VALUES are not trusted at all: the launchpad
/// computes them on-chain from the public book (rung-1 REPLAYABLE). What these
/// tests establish is that the gate is REAL (a forged proof cannot pass a real
/// pairing) and BOUND (a genuine proof for launch A cannot attest launch B).
///
/// ⚠ dev-ceremony: the registry's epoch-0 VK is a single-party dev setup — a
/// DEMO OF THE INTERFACE, not production trust (`OCIP-SECURITY-SOCKET.md`).
contract DreggLaunchpadProofAttestorTest is Test {
    DreggGroth16VerifierUpgradeable registry;
    DreggVerifier socket;
    DreggLaunchpad pad;
    DreggProofAttestor att;

    // The REAL proof fixture, split into the socket's typed Proof + Statement.
    DreggAttestation.Proof proof;
    DreggAttestation.Statement stmt;

    address binder = makeAddr("binder");
    address creator = makeAddr("creator");
    address alice = makeAddr("alice");
    address bob = makeAddr("bob");

    uint64 constant COMMIT_DUR = 100;
    uint64 constant REVEAL_DUR = 100;
    uint256 constant G = 1e9;

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

        registry = new DreggGroth16VerifierUpgradeable();
        socket = new DreggVerifier(IGroth16VerifierRegistry(address(registry)));
        pad = new DreggLaunchpad(IDeployerGate(address(0))); // permissionless deploy
        // The attestor trusts the ONE dregg instance the fixture is about.
        att = new DreggProofAttestor(IDreggVerifier(address(socket)), pad, stmt.genesisRoot, binder);

        vm.deal(creator, 1 ether);
        vm.deal(alice, 1 ether);
        vm.deal(bob, 1 ether);
    }

    // ─── helpers ────────────────────────────────────────────────────────────────

    function _schedule() internal pure returns (DreggLaunchpad.Schedule memory s) {
        s = DreggLaunchpad.Schedule({
            totalSupply: 1200,
            saleSupply: 1000,
            creatorAllocation: 100,
            poolAllocation: 100,
            graduationBps: 5000,
            creatorLockUntil: 0,
            reservePrice: 1 * G
        });
    }

    function _register() internal returns (uint256 id) {
        vm.prank(creator);
        id = pad.registerLaunch(
            "DreggMeme", "DMEME", _schedule(), COMMIT_DUR, REVEAL_DUR, ILaunchEligibility(address(0)), att, ""
        );
    }

    function _commit(uint256 id, address who, uint256 price, uint256 qty, bytes32 salt) internal {
        bytes32 seal = pad.sealOf(price, qty, salt, who);
        vm.prank(who);
        pad.commitBid{value: price * qty}(id, seal, "");
    }

    /// The blob `finalizeClearing` forwards to the attestor.
    function _blob(DreggAttestation.Proof memory p, DreggAttestation.Statement memory s)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encode(p, s);
    }

    /// Two revealed bidders on `id`: alice(5G,400) index 0, bob(3G,400) index 1.
    /// Clearing walk fills both (800 <= saleSupply 1000) → uniform price = 3G.
    function _setupTwoRevealed(uint256 id) internal {
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(alice);
        pad.revealBid(id, 5 * G, 400, keccak256("a"));
        vm.prank(bob);
        pad.revealBid(id, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + REVEAL_DUR);
    }

    function _order() internal pure returns (uint256[] memory o) {
        o = new uint256[](2);
        o[0] = 0; // alice 5G first — descending
        o[1] = 1; // bob 3G
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (1) THE HONEST POLE — a bound, REAL dregg proof attests → the launch clears
    // ══════════════════════════════════════════════════════════════════════════

    /// The fixture proof really does verify through the socket (the accept path
    /// is a real BN254 pairing, not a mock) — asserted here so every negative
    /// below is non-vacuous.
    function test_FixtureProofIsGenuinelyValid() public view {
        assertTrue(socket.verifyStatement(proof, stmt), "the real wrap proof must verify");
    }

    /// POLARITY 1 — bound + valid → attested → `finalizeClearing` proceeds and
    /// the launch reaches `Cleared` with `clearingAttested` set.
    function test_BoundRealProofAttestsAndLaunchClears() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);

        _setupTwoRevealed(id);
        pad.finalizeClearing(id, _order(), _blob(proof, stmt));

        (uint256 price, uint256 sold, bool attested) = _clearingOf(id);
        assertEq(price, 3 * G, "uniform clearing price = the marginal winning bid");
        assertEq(sold, 800);
        assertTrue(attested, "clearingAttested must be set by the PROOF arm");
        assertEq(uint256(pad.phaseOf(id)), uint256(DreggLaunchpad.Phase.Cleared));
    }

    /// The attestor answers TRUE for the bound launch — the seam itself, read
    /// directly (independent of the launchpad's plumbing).
    function test_AttestorReturnsTrueForBoundLaunch() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);
        assertTrue(
            att.attestClearing(id, 1000, 3 * G, keccak256("any book"), _blob(proof, stmt)),
            "a bound, valid proof attests"
        );
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (2) THE NEGATIVE POLE — typed refusals, launch stays pre-final
    // ══════════════════════════════════════════════════════════════════════════

    /// ⚑ THE LAUNCH BINDING (the unbound-attestation bug, refused).
    ///
    /// A GENUINE, VERIFYING proof — the very one that legitimately attests
    /// launch A — presented to launch B, which is bound to a different dregg
    /// transition. It must NOT attest B. Without the `statementDigest` binding
    /// this proof would sail through the pairing and clear B: that is exactly
    /// the "an audit cleared for one disclosure authorized any other" hole.
    ///
    /// MUTATION CANARY: delete the `statementDigest(s) != bnd.statementDigest`
    /// check in `DreggProofAttestor.attestClearing` and this test goes RED.
    function test_WrongLaunchProofIsRefused() public {
        uint256 idA = _register();
        uint256 idB = _register();

        // A is bound to the fixture's real transition.
        vm.prank(binder);
        att.bindLaunch(idA, _schedule(), stmt);

        // B is bound to a DIFFERENT dregg transition (same trusted instance).
        DreggAttestation.Statement memory other = stmt;
        other.finalRoot[0] = other.finalRoot[0] + 1;
        vm.prank(binder);
        att.bindLaunch(idB, _schedule(), other);

        // The proof is genuine and verifies — but it is A's, not B's.
        assertTrue(socket.verifyStatement(proof, stmt), "precondition: the proof is real");
        assertFalse(
            att.attestClearing(idB, 1000, 3 * G, keccak256("book"), _blob(proof, stmt)),
            "a proof bound to launch A must never attest launch B"
        );

        // ...and the launchpad refuses B with the typed reason.
        _setupTwoRevealed(idB);
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(idB, _order(), _blob(proof, stmt));
        assertEq(uint256(pad.phaseOf(idB)), uint256(DreggLaunchpad.Phase.Reveal), "B stays pre-final");
    }

    /// An UNBOUND launch attests nothing, even with a genuine proof — the binder
    /// must have designated a transition first.
    function test_UnboundLaunchIsRefused() public {
        uint256 id = _register();
        _setupTwoRevealed(id);

        assertFalse(att.attestClearing(id, 1000, 3 * G, keccak256("book"), _blob(proof, stmt)));
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, _order(), _blob(proof, stmt));
    }

    /// A FORGED proof: a tampered proof point fails the real BN254 pairing → the
    /// socket returns false → the launchpad refuses. (The statement is untouched,
    /// so the binding passes and the PAIRING is what rejects — this is the
    /// crypto tooth, not the binding tooth.)
    function test_ForgedProofIsRefused() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);
        _setupTwoRevealed(id);

        DreggAttestation.Proof memory bad = proof;
        bad.a[0] = bad.a[0] + 1;

        assertFalse(att.attestClearing(id, 1000, 3 * G, keccak256("book"), _blob(bad, stmt)));
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, _order(), _blob(bad, stmt));
    }

    /// A LIED-ABOUT final root: the real proof presented with a statement it does
    /// not attest. Caught by the BINDING first (the digest moves), and it would
    /// fail the pairing anyway — belt and braces.
    function test_LiedFinalRootIsRefused() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);

        DreggAttestation.Statement memory lied = stmt;
        lied.finalRoot[0] = lied.finalRoot[0] + 1;
        assertFalse(socket.verifyStatement(proof, lied), "the pairing rejects it too");
        assertFalse(att.attestClearing(id, 1000, 3 * G, keccak256("book"), _blob(proof, lied)));
    }

    /// An ABSENT / malformed proof blob decodes to nothing → false, never a
    /// revert inside the view (the launchpad supplies the typed reason).
    function test_MalformedAndEmptyProofBlobsAreRefused() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);
        _setupTwoRevealed(id);

        assertFalse(att.attestClearing(id, 1000, 3 * G, keccak256("book"), ""), "empty blob");
        assertFalse(att.attestClearing(id, 1000, 3 * G, keccak256("book"), hex"deadbeef"), "garbage blob");

        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, _order(), hex"deadbeef");
    }

    /// A non-canonical (out-of-field) lane makes the statement ILL-FORMED — the
    /// socket reverts `NonCanonicalLane`; the attestor stays fail-closed and
    /// reports false rather than bricking the launch.
    function test_NonCanonicalLaneIsRefusedNotReverted() public {
        uint256 id = _register();
        DreggAttestation.Statement memory bad = stmt;
        bad.finalRoot[0] = 2013265921; // == BABYBEAR_P, out of field
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), bad); // ill-formed, but bindable
        assertFalse(att.attestClearing(id, 1000, 3 * G, keccak256("book"), _blob(proof, bad)));
    }

    /// A refused attestation leaves the launch pre-final and REFUNDABLE — a
    /// binder that never lands a valid proof is a liveness fault, not a theft.
    function test_RefusedAttestationStaysRefundable() public {
        uint256 id = _register();
        _setupTwoRevealed(id); // never bound → can never attest

        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, _order(), _blob(proof, stmt));

        vm.warp(block.timestamp + pad.REFUND_GRACE());
        uint256 before = alice.balance;
        vm.prank(alice);
        pad.reclaimEscrow(id);
        assertEq(alice.balance, before + 5 * G * 400, "escrow fully reclaimed");
    }

    /// The `saleSupply` the launchpad clears must be the DISCLOSED, committed one
    /// the binding recorded (read the seam directly — the launchpad always passes
    /// its own committed supply, so this arm is the attestor's own guard).
    function test_WrongSaleSupplyIsRefused() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);
        assertFalse(
            att.attestClearing(id, 999, 3 * G, keccak256("book"), _blob(proof, stmt)),
            "a supply other than the committed one attests nothing"
        );
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (3) THE BINDING'S OWN TEETH
    // ══════════════════════════════════════════════════════════════════════════

    function test_OnlyBinderCanBind() public {
        uint256 id = _register();
        vm.expectRevert(abi.encodeWithSelector(DreggProofAttestor.NotBinder.selector, address(this)));
        att.bindLaunch(id, _schedule(), stmt);
    }

    /// One-shot: the binder picks ONE transition per launch and can never swap it
    /// (in particular, not after seeing the clearing).
    function test_BindIsOneShot() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);
        vm.prank(binder);
        vm.expectRevert(abi.encodeWithSelector(DreggProofAttestor.AlreadyBound.selector, id));
        att.bindLaunch(id, _schedule(), stmt);
    }

    /// The binder cannot bind a launch under params the launch never committed —
    /// the binding is tied to the on-chain `scheduleCommit`.
    function test_BindRejectsUncommittedSchedule() public {
        uint256 id = _register();
        DreggLaunchpad.Schedule memory lied = _schedule();
        lied.saleSupply = 999; // not what was committed
        vm.prank(binder);
        vm.expectRevert(abi.encodeWithSelector(DreggProofAttestor.ScheduleMismatch.selector, id));
        att.bindLaunch(id, lied, stmt);
    }

    function test_BindRejectsNoSuchLaunch() public {
        vm.prank(binder);
        vm.expectRevert(abi.encodeWithSelector(DreggProofAttestor.NoSuchLaunch.selector, uint256(4242)));
        att.bindLaunch(4242, _schedule(), stmt);
    }

    /// A statement about a FOREIGN dregg instance can never be bound.
    function test_BindRejectsForeignDreggInstance() public {
        uint256 id = _register();
        DreggAttestation.Statement memory foreign = stmt;
        foreign.genesisRoot[0] = foreign.genesisRoot[0] + 1;
        vm.prank(binder);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggProofAttestor.UntrustedDreggInstance.selector,
                DreggAttestation.packLanes(foreign.genesisRoot),
                DreggAttestation.packLanes(stmt.genesisRoot)
            )
        );
        att.bindLaunch(id, _schedule(), foreign);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (4) VK ROTATION IS ABSORBED BY THE REGISTRY — the launchpad pins no VK
    // ══════════════════════════════════════════════════════════════════════════

    /// Rotating the registry's VK changes what attests, with NO change to the
    /// launchpad, the launch, or the attestor. Under a rotated (broken) VK the
    /// same proof stops attesting; the attestor tracks the registry's current
    /// epoch rather than pinning one.
    function test_VkRotationIsAbsorbedByTheRegistry() public {
        uint256 id = _register();
        vm.prank(binder);
        att.bindLaunch(id, _schedule(), stmt);
        // Build the revealed book NOW, while the commit/reveal windows are open —
        // the timelocked VK rotation below warps time forward past them (but still
        // well inside the launchpad's 7-day clearing/refund grace).
        _setupTwoRevealed(id);
        assertEq(att.currentEpoch(), 0);
        assertTrue(att.attestClearing(id, 1000, 3 * G, keccak256("book"), _blob(proof, stmt)));

        // Rotate to a VK the proof was NOT minted under (alpha := the G1
        // generator — on-curve and in-field, so it validates, but the pairing
        // fails). Same pattern as `DreggSocket.t.sol`. The flip is TIMELOCKED:
        // propose, wait out the mandatory delay, activate.
        DreggGroth16VerifierUpgradeable.VerifyingKey memory vk = registry.getVerifyingKey(0);
        vk.alpha.x = 1;
        vk.alpha.y = 2;
        registry.proposeEpoch(vk);
        vm.warp(block.timestamp + registry.TIMELOCK_DELAY() + 1);
        registry.activateEpoch();

        assertEq(att.currentEpoch(), 1, "the attestor follows the registry, pins nothing");
        assertFalse(
            att.attestClearing(id, 1000, 3 * G, keccak256("book"), _blob(proof, stmt)),
            "an old-epoch proof does not attest under the new VK"
        );

        // Still within the clearing window (~2 days < REFUND_GRACE 7 days), so
        // finalize runs — and is refused for lack of a valid attestation.
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, _order(), _blob(proof, stmt));
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (5) CONSTRUCTOR FAIL-CLOSED
    // ══════════════════════════════════════════════════════════════════════════

    function test_ConstructorRejectsCodelessSocket() public {
        vm.expectRevert(abi.encodeWithSelector(DreggProofAttestor.SocketHasNoCode.selector, address(0xdead)));
        new DreggProofAttestor(IDreggVerifier(address(0xdead)), pad, stmt.genesisRoot, binder);
    }

    function test_ConstructorRejectsCodelessLaunchpad() public {
        vm.expectRevert(abi.encodeWithSelector(DreggProofAttestor.LaunchpadHasNoCode.selector, address(0xbeef)));
        new DreggProofAttestor(IDreggVerifier(address(socket)), DreggLaunchpad(address(0xbeef)), stmt.genesisRoot, binder);
    }

    function test_ConstructorRejectsZeroBinder() public {
        vm.expectRevert(DreggProofAttestor.ZeroBinder.selector);
        new DreggProofAttestor(IDreggVerifier(address(socket)), pad, stmt.genesisRoot, address(0));
    }

    // ─── plumbing ───────────────────────────────────────────────────────────────

    function _clearingOf(uint256 id) internal view returns (uint256 price, uint256 sold, bool attested) {
        return (pad.clearingPriceOf(id), pad.soldQtyOf(id), pad.clearingAttested(id));
    }
}
