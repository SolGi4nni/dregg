// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";
import {CommitteeAttestor} from "../contracts/launchpad/CommitteeAttestor.sol";
import {DreggProofAttestor} from "../contracts/launchpad/DreggProofAttestor.sol";
import {ConjunctiveAttestor} from "../contracts/launchpad/ConjunctiveAttestor.sol";
import {IDeployerGate} from "../contracts/launchpad/IDeployerGate.sol";
import {DreggVerifier, IDreggVerifier, DreggAttestation} from "../contracts/socket/DreggVerifier.sol";
import {DreggGroth16VerifierUpgradeable} from "../contracts/DreggGroth16VerifierUpgradeable.sol";
import {IGroth16VerifierRegistry} from "../contracts/IGroth16VerifierRegistry.sol";

/// THE PLUGGABILITY, DEMONSTRATED — the launchpad pins the `IClearingAttestor`
/// SEAM, never an arm. Here BOTH arms are wired at once: a real k-of-n committee
/// signature AND a real dregg Groth16 proof (verified through the OCIP socket)
/// must attest, or the launch does not clear.
///
/// The launchpad is UNCHANGED and unaware: `ConjunctiveAttestor` is itself just
/// an `IClearingAttestor`. Committee-only, proof-only, both, or neither are all
/// deployment choices, not code changes.
contract DreggLaunchpadConjunctiveAttestorTest is Test {
    DreggGroth16VerifierUpgradeable registry;
    DreggVerifier socket;
    DreggLaunchpad pad;
    DreggProofAttestor proofAtt;
    CommitteeAttestor committee;
    ConjunctiveAttestor conj;

    DreggAttestation.Proof proof;
    DreggAttestation.Statement stmt;

    uint256 constant PK1 = 0xA11CE;
    uint256 constant PK2 = 0xB0B;
    uint256 constant PK3 = 0xCACA0;

    address binder = makeAddr("binder");
    address creator = makeAddr("creator");
    address alice = makeAddr("alice");
    address bob = makeAddr("bob");

    uint64 constant COMMIT_DUR = 100;
    uint64 constant REVEAL_DUR = 100;
    uint256 constant G = 1e9;
    uint256 constant SALE_SUPPLY = 1000;

    function setUp() public {
        string memory json = vm.readFile("test/fixtures/settlement_groth16.json");
        string[] memory pw = vm.parseJsonStringArray(json, ".proof");
        proof.a = [vm.parseUint(pw[0]), vm.parseUint(pw[1])];
        proof.b = [[vm.parseUint(pw[2]), vm.parseUint(pw[3])], [vm.parseUint(pw[4]), vm.parseUint(pw[5])]];
        proof.c = [vm.parseUint(pw[6]), vm.parseUint(pw[7])];
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
        pad = new DreggLaunchpad(IDeployerGate(address(0)));
        proofAtt = new DreggProofAttestor(IDreggVerifier(address(socket)), pad, stmt.genesisRoot, binder);

        address[] memory signers = new address[](3);
        signers[0] = vm.addr(PK1);
        signers[1] = vm.addr(PK2);
        signers[2] = vm.addr(PK3);
        committee = new CommitteeAttestor(pad, signers, 2);

        IClearingAttestor[] memory arms = new IClearingAttestor[](2);
        arms[0] = IClearingAttestor(address(committee));
        arms[1] = IClearingAttestor(address(proofAtt));
        conj = new ConjunctiveAttestor(arms);

        vm.deal(creator, 1 ether);
        vm.deal(alice, 1 ether);
        vm.deal(bob, 1 ether);
    }

    // ─── helpers ────────────────────────────────────────────────────────────────

    function _schedule() internal pure returns (DreggLaunchpad.Schedule memory s) {
        s = DreggLaunchpad.Schedule({
            totalSupply: 1200,
            saleSupply: SALE_SUPPLY,
            creatorAllocation: 100,
            poolAllocation: 100,
            graduationBps: 5000,
            creatorLockUntil: 0,
            reservePrice: 1 * G
        });
    }

    /// Register a launch behind the CONJUNCTION and bind the proof arm to it.
    function _registerAndBind() internal returns (uint256 id) {
        vm.prank(creator);
        id = pad.registerLaunch(
            "DreggMeme",
            "DMEME",
            _schedule(),
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(conj)),
            ""
        );
        vm.prank(binder);
        proofAtt.bindLaunch(id, _schedule(), stmt);
    }

    function _setupTwoRevealed(uint256 id) internal {
        bytes32 sa = keccak256("a");
        bytes32 sb = keccak256("b");
        // Compute the seals BEFORE pranking — `sealOf` is itself a call and
        // would otherwise consume the prank.
        bytes32 sealA = pad.sealOf(5 * G, 400, sa, alice);
        bytes32 sealB = pad.sealOf(3 * G, 400, sb, bob);
        vm.prank(alice);
        pad.commitBid{value: 5 * G * 400}(id, sealA, "");
        vm.prank(bob);
        pad.commitBid{value: 3 * G * 400}(id, sealB, "");
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(alice);
        pad.revealBid(id, 5 * G, 400, sa);
        vm.prank(bob);
        pad.revealBid(id, 3 * G, 400, sb);
        vm.warp(block.timestamp + REVEAL_DUR);
    }

    function _order() internal pure returns (uint256[] memory o) {
        o = new uint256[](2);
        o[0] = 0;
        o[1] = 1;
    }

    /// The launchpad's book-commit fold for the standard two-bidder clear.
    function _bookCommit() internal view returns (bytes32 acc) {
        acc = keccak256(abi.encodePacked(acc, alice, uint256(5 * G), uint256(400)));
        acc = keccak256(abi.encodePacked(acc, bob, uint256(3 * G), uint256(400)));
    }

    /// A valid 2-of-3 committee blob over the clearing tuple.
    function _committeeBlob(uint256 id) internal view returns (bytes memory) {
        bytes32 digest = committee.attestationDigest(id, SALE_SUPPLY, 3 * G, _bookCommit());
        uint256[] memory pks = new uint256[](2);
        // ascending by signer address (the attestor's dedup discipline)
        (pks[0], pks[1]) = vm.addr(PK1) < vm.addr(PK2) ? (PK1, PK2) : (PK2, PK1);
        bytes[] memory sigs = new bytes[](2);
        for (uint256 i = 0; i < 2; i++) {
            (uint8 v, bytes32 r, bytes32 s) = vm.sign(pks[i], digest);
            sigs[i] = abi.encodePacked(r, s, v);
        }
        return abi.encode(sigs);
    }

    function _conjBlob(bytes memory committeeArm, bytes memory proofArm) internal pure returns (bytes memory) {
        bytes[] memory arms = new bytes[](2);
        arms[0] = committeeArm;
        arms[1] = proofArm;
        return abi.encode(arms);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // THE HONEST POLE — both arms attest → the launch clears
    // ══════════════════════════════════════════════════════════════════════════

    function test_BothArmsAttestAndLaunchClears() public {
        uint256 id = _registerAndBind();
        _setupTwoRevealed(id);

        pad.finalizeClearing(id, _order(), _conjBlob(_committeeBlob(id), abi.encode(proof, stmt)));

        assertEq(pad.clearingPriceOf(id), 3 * G);
        assertEq(pad.soldQtyOf(id), 800);
        assertTrue(pad.clearingAttested(id), "attested by committee AND proof");
        assertEq(uint256(pad.phaseOf(id)), uint256(DreggLaunchpad.Phase.Cleared));
        assertEq(conj.armCount(), 2);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // THE NEGATIVE POLE — either arm refusing is enough to refuse the whole
    // ══════════════════════════════════════════════════════════════════════════

    /// A real PROOF does not rescue a missing committee quorum.
    function test_ProofArmAloneIsNotEnough() public {
        uint256 id = _registerAndBind();
        _setupTwoRevealed(id);

        bytes[] memory none = new bytes[](0); // no signatures at all
        bytes memory blob = _conjBlob(abi.encode(none), abi.encode(proof, stmt));

        assertFalse(conj.attestClearing(id, SALE_SUPPLY, 3 * G, _bookCommit(), blob));
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, _order(), blob);
    }

    /// A real COMMITTEE quorum does not rescue a forged proof — the pairing still
    /// has to pass. (This is the tooth the committee alone never had.)
    function test_CommitteeArmAloneIsNotEnough() public {
        uint256 id = _registerAndBind();
        _setupTwoRevealed(id);

        DreggAttestation.Proof memory bad = proof;
        bad.a[0] = bad.a[0] + 1;
        bytes memory blob = _conjBlob(_committeeBlob(id), abi.encode(bad, stmt));

        assertFalse(conj.attestClearing(id, SALE_SUPPLY, 3 * G, _bookCommit(), blob));
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, _order(), blob);
    }

    function test_WrongArmCountIsRefused() public {
        uint256 id = _registerAndBind();
        bytes[] memory one = new bytes[](1);
        one[0] = _committeeBlob(id);
        assertFalse(conj.attestClearing(id, SALE_SUPPLY, 3 * G, _bookCommit(), abi.encode(one)));
    }

    function test_MalformedEnvelopeIsRefused() public {
        uint256 id = _registerAndBind();
        assertFalse(conj.attestClearing(id, SALE_SUPPLY, 3 * G, _bookCommit(), hex"deadbeef"));
        assertFalse(conj.attestClearing(id, SALE_SUPPLY, 3 * G, _bookCommit(), ""));
    }

    // ─── constructor fail-closed ────────────────────────────────────────────────

    function test_ConstructorRejectsNoArms() public {
        IClearingAttestor[] memory empty = new IClearingAttestor[](0);
        vm.expectRevert(ConjunctiveAttestor.NoArms.selector);
        new ConjunctiveAttestor(empty);
    }

    function test_ConstructorRejectsDuplicateArm() public {
        IClearingAttestor[] memory dup = new IClearingAttestor[](2);
        dup[0] = IClearingAttestor(address(committee));
        dup[1] = IClearingAttestor(address(committee));
        vm.expectRevert(abi.encodeWithSelector(ConjunctiveAttestor.DuplicateArm.selector, address(committee)));
        new ConjunctiveAttestor(dup);
    }

    function test_ConstructorRejectsCodelessArm() public {
        IClearingAttestor[] memory bad = new IClearingAttestor[](1);
        bad[0] = IClearingAttestor(address(0xdead));
        vm.expectRevert(abi.encodeWithSelector(ConjunctiveAttestor.ArmHasNoCode.selector, address(0xdead)));
        new ConjunctiveAttestor(bad);
    }

    function test_ConstructorRejectsZeroArm() public {
        IClearingAttestor[] memory bad = new IClearingAttestor[](1);
        bad[0] = IClearingAttestor(address(0));
        vm.expectRevert(ConjunctiveAttestor.ZeroArm.selector);
        new ConjunctiveAttestor(bad);
    }
}
