// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggCredentialGate.sol";

/// @dev Mock SP1 Verifier that always succeeds (shared pattern with vault tests).
contract MockSP1VerifierForGate {
    bool public shouldPass = true;

    function setShouldPass(bool _pass) external {
        shouldPass = _pass;
    }

    function verifyProof(
        bytes32, /* vkey */
        bytes calldata, /* publicValues */
        bytes calldata /* proofBytes */
    ) external view {
        require(shouldPass, "MockSP1Verifier: proof rejected");
    }
}

contract DreggCredentialGateTest is Test {
    DreggCredentialGate public gate;
    MockSP1VerifierForGate public verifier;

    bytes32 constant PROGRAM_VKEY = bytes32(uint256(0xcafe));
    bytes32 constant FED_ROOT = bytes32(uint256(0xfed));
    bytes32 constant PRED_HASH = keccak256("age >= 18");

    address admin = address(this);
    address user = address(0xBEEF);

    function setUp() public {
        verifier = new MockSP1VerifierForGate();
        gate = new DreggCredentialGate(address(verifier), PROGRAM_VKEY, admin);

        // Trust our test federation root.
        gate.setFederationTrust(FED_ROOT, true);
    }

    // ─── #13 proof builders (presenter + action binding) ────────────────────
    /// Public values for a mint proof bound to `sender` + `tokenId`.
    function _mintPV(address sender, uint256 tokenId, bytes32 nullifier)
        internal
        view
        returns (bytes memory)
    {
        bytes32 action = keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_MINT(), tokenId));
        return abi.encode(true, FED_ROOT, PRED_HASH, nullifier, sender, action);
    }

    function _mintProof(address sender, uint256 tokenId, bytes32 nullifier)
        internal
        view
        returns (bytes memory)
    {
        return abi.encode(hex"5678", _mintPV(sender, tokenId, nullifier));
    }

    /// Public values for a vote proof bound to `sender` + `proposalId` + `support`.
    function _votePV(address sender, uint256 proposalId, bool support, bytes32 nullifier)
        internal
        view
        returns (bytes memory)
    {
        bytes32 action =
            keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_VOTE(), proposalId, support));
        return abi.encode(true, FED_ROOT, PRED_HASH, nullifier, sender, action);
    }

    function _voteProof(address sender, uint256 proposalId, bool support, bytes32 nullifier)
        internal
        view
        returns (bytes memory)
    {
        return abi.encode(hex"707e", _votePV(sender, proposalId, support, nullifier));
    }

    // ─── Admin / VK Governance ──────────────────────────────────────────────

    function test_adminCanSetFederationTrust() public {
        bytes32 newRoot = bytes32(uint256(0xabc));
        gate.setFederationTrust(newRoot, true);
        assertTrue(gate.trustedFederations(newRoot));
    }

    function test_adminCanRevokeFederationTrust() public {
        gate.setFederationTrust(FED_ROOT, false);
        assertFalse(gate.trustedFederations(FED_ROOT));
    }

    function test_nonAdminCannotSetFederationTrust() public {
        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.setFederationTrust(FED_ROOT, false);
    }

    // ─── Credential Verification ────────────────────────────────────────────

    function test_verifyCredentialReturnsTrue() public view {
        bytes32 nullifier = keccak256("verifyNull");
        bytes memory publicValues = abi.encode(true, FED_ROOT, PRED_HASH, nullifier);
        bytes memory proofBytes = hex"1234";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        bool result = gate.verifyCredential(FED_ROOT, PRED_HASH, sp1Proof);
        assertTrue(result);
    }

    function test_verifyCredentialRevertsUntrustedFederation() public {
        bytes32 untrusted = bytes32(uint256(0x999));
        bytes memory sp1Proof = abi.encode(hex"1234", abi.encode(true, untrusted, PRED_HASH, bytes32(0)));

        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.UntrustedFederation.selector, untrusted));
        gate.verifyCredential(untrusted, PRED_HASH, sp1Proof);
    }

    function test_verifyCredentialReturnsFalseOnInvalidProof() public {
        verifier.setShouldPass(false);
        bytes memory sp1Proof = abi.encode(hex"bad0", abi.encode(true, FED_ROOT, PRED_HASH, bytes32(0)));

        bool result = gate.verifyCredential(FED_ROOT, PRED_HASH, sp1Proof);
        assertFalse(result);
    }

    // ─── Mint With Credential ───────────────────────────────────────────────

    function test_mintWithCredential() public {
        uint256 tokenId = 1;
        bytes32 nullifier = keccak256("mintNull1");
        bytes memory sp1Proof = _mintProof(user, tokenId, nullifier);

        vm.prank(user);
        gate.mintWithCredential(tokenId, FED_ROOT, PRED_HASH, sp1Proof);

        assertEq(gate.tokenOwner(tokenId), user);
        assertEq(gate.balanceOf(user), 1);
        // The bare presentation nullifier is the replay key: one mint per credential.
        assertTrue(gate.usedNullifiers(nullifier));
    }

    function test_mintRejectsDuplicateNullifierSameToken() public {
        // Replaying the same nullifier against the SAME tokenId must revert.
        bytes32 nullifier = keccak256("mintNull2");
        bytes memory sp1Proof = _mintProof(user, 1, nullifier);

        vm.prank(user);
        gate.mintWithCredential(1, FED_ROOT, PRED_HASH, sp1Proof);

        vm.prank(user);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.NullifierAlreadyUsed.selector, nullifier));
        gate.mintWithCredential(1, FED_ROOT, PRED_HASH, sp1Proof);
    }

    function test_mintRejectsReplayAcrossTokenIds() public {
        // SOUNDNESS: one credential presentation (one nullifier) must NOT mint a
        // second (different) tokenId. Under the #13 action binding each proof is
        // bound to its tokenId, so the attacker must build a FRESH presentation for
        // tokenId 11 — but it reuses the same credential nullifier, and the bare
        // nullifier is the replay key: the second mint reverts.
        bytes32 nullifier = keccak256("mintNull3");
        // Build proofs BEFORE pranking (the helper's view call consumes the prank).
        bytes memory proof10 = _mintProof(user, 10, nullifier);
        bytes memory proof11 = _mintProof(user, 11, nullifier);

        vm.prank(user);
        gate.mintWithCredential(10, FED_ROOT, PRED_HASH, proof10);

        vm.prank(user);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.NullifierAlreadyUsed.selector, nullifier));
        gate.mintWithCredential(11, FED_ROOT, PRED_HASH, proof11);

        assertEq(gate.tokenOwner(10), user);
        assertEq(gate.tokenOwner(11), address(0));
        assertEq(gate.balanceOf(user), 1);
    }

    function test_mintRejectsAlreadyMintedToken() public {
        uint256 tokenId = 42;
        bytes32 null1 = keccak256("mintNullA");
        bytes32 null2 = keccak256("mintNullB");

        // Build proofs BEFORE pranking (the helper's `gate.ACTION_MINT()` view call
        // would otherwise consume the prank meant for the mint).
        address user2 = address(0xCAFE);
        bytes memory proof1 = _mintProof(user, tokenId, null1);
        bytes memory proof2 = _mintProof(user2, tokenId, null2);

        vm.prank(user);
        gate.mintWithCredential(tokenId, FED_ROOT, PRED_HASH, proof1);

        // Different user, with their OWN valid proof for the same tokenId, still
        // can't mint it — it is already owned.
        vm.prank(user2);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.TokenAlreadyMinted.selector, tokenId));
        gate.mintWithCredential(tokenId, FED_ROOT, PRED_HASH, proof2);
    }

    // ─── Vote With Credential ───────────────────────────────────────────────

    function test_voteWithCredential() public {
        uint256 proposalId = 7;
        bytes32 nullifier = keccak256("voteNull1");
        bytes memory sp1Proof = _voteProof(user, proposalId, true, nullifier);

        vm.prank(user);
        gate.voteWithCredential(proposalId, true, FED_ROOT, PRED_HASH, sp1Proof);

        (uint256 yes, uint256 no) = gate.getVotes(proposalId);
        assertEq(yes, 1);
        assertEq(no, 0);
    }

    function test_voteRejectsDoubleVote() public {
        uint256 proposalId = 8;
        bytes32 nullifier = keccak256("voteNull2");
        // Build proofs BEFORE pranking (the helper's view call consumes the prank).
        bytes memory yesProof = _voteProof(user, proposalId, true, nullifier);
        bytes memory noProof = _voteProof(user, proposalId, false, nullifier);

        vm.prank(user);
        gate.voteWithCredential(proposalId, true, FED_ROOT, PRED_HASH, yesProof);

        // Flipping to the opposite side needs a proof bound to (proposalId, false),
        // but that fresh presentation reuses the same per-proposal nullifier → the
        // per-proposal nullifier blocks the second vote.
        vm.prank(user);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.AlreadyVoted.selector, proposalId, nullifier));
        gate.voteWithCredential(proposalId, false, FED_ROOT, PRED_HASH, noProof);
    }

    function test_voteAllowsSameNullifierDifferentProposal() public {
        bytes32 nullifier1 = keccak256("voteMulti1");
        bytes32 nullifier2 = keccak256("voteMulti2");
        // Build proofs BEFORE pranking (the helper's view call consumes the prank).
        bytes memory proofP1 = _voteProof(user, 1, true, nullifier1);
        bytes memory proofP2 = _voteProof(user, 2, false, nullifier2);

        vm.prank(user);
        gate.voteWithCredential(1, true, FED_ROOT, PRED_HASH, proofP1);

        vm.prank(user);
        gate.voteWithCredential(2, false, FED_ROOT, PRED_HASH, proofP2);

        (uint256 yes1, ) = gate.getVotes(1);
        (, uint256 no2) = gate.getVotes(2);
        assertEq(yes1, 1);
        assertEq(no2, 1);
    }

    // ─── #13 Proof-Binding (presenter + action) ─────────────────────────────

    address constant SNIPER = address(0x5715E5);

    /// A proof BOUND to `user` cannot be sniped from the mempool and presented by a
    /// different msg.sender to steal the mint.
    function test_mintSnipedByDifferentSenderRejected() public {
        bytes32 nullifier = keccak256("snipeMint");
        // The proof is bound to `user` (the legitimate presenter).
        bytes memory sp1Proof = _mintProof(user, 1, nullifier);

        // The sniper front-runs with the SAME proof but their own msg.sender.
        vm.prank(SNIPER);
        vm.expectRevert(
            abi.encodeWithSelector(DreggCredentialGate.SenderBindingMismatch.selector, user, SNIPER)
        );
        gate.mintWithCredential(1, FED_ROOT, PRED_HASH, sp1Proof);

        // The legitimate presenter still mints with their own proof.
        vm.prank(user);
        gate.mintWithCredential(1, FED_ROOT, PRED_HASH, sp1Proof);
        assertEq(gate.tokenOwner(1), user);
    }

    /// A proof bound to tokenId 5 cannot be redirected to mint a different tokenId.
    function test_mintForDifferentTokenIdRejected() public {
        bytes32 nullifier = keccak256("redirMint");
        bytes memory sp1Proof = _mintProof(user, 5, nullifier); // bound to tokenId 5

        bytes32 boundAction = keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_MINT(), uint256(5)));
        bytes32 wantAction = keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_MINT(), uint256(6)));
        vm.prank(user);
        vm.expectRevert(
            abi.encodeWithSelector(DreggCredentialGate.ActionBindingMismatch.selector, boundAction, wantAction)
        );
        gate.mintWithCredential(6, FED_ROOT, PRED_HASH, sp1Proof);
    }

    /// A vote proof bound to `support = true` cannot be flipped to the OPPOSITE side.
    function test_voteFlipSupportRejected() public {
        bytes32 nullifier = keccak256("flipVote");
        bytes memory sp1Proof = _voteProof(user, 3, true, nullifier); // bound to (3, true)

        bytes32 boundAction = keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_VOTE(), uint256(3), true));
        bytes32 wantAction = keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_VOTE(), uint256(3), false));
        vm.prank(user);
        vm.expectRevert(
            abi.encodeWithSelector(DreggCredentialGate.ActionBindingMismatch.selector, boundAction, wantAction)
        );
        gate.voteWithCredential(3, false, FED_ROOT, PRED_HASH, sp1Proof);
    }

    /// A vote proof bound to proposal 3 cannot be replayed to vote on every proposal.
    function test_voteForDifferentProposalRejected() public {
        bytes32 nullifier = keccak256("everyVote");
        bytes memory sp1Proof = _voteProof(user, 3, true, nullifier); // bound to proposal 3

        bytes32 boundAction = keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_VOTE(), uint256(3), true));
        bytes32 wantAction = keccak256(abi.encode(address(gate), block.chainid, gate.ACTION_VOTE(), uint256(4), true));
        vm.prank(user);
        vm.expectRevert(
            abi.encodeWithSelector(DreggCredentialGate.ActionBindingMismatch.selector, boundAction, wantAction)
        );
        gate.voteWithCredential(4, true, FED_ROOT, PRED_HASH, sp1Proof);
    }

    /// A vote proof bound to `user` cannot be sniped by a different msg.sender.
    function test_voteSnipedByDifferentSenderRejected() public {
        bytes32 nullifier = keccak256("snipeVote");
        bytes memory sp1Proof = _voteProof(user, 9, true, nullifier);

        vm.prank(SNIPER);
        vm.expectRevert(
            abi.encodeWithSelector(DreggCredentialGate.SenderBindingMismatch.selector, user, SNIPER)
        );
        gate.voteWithCredential(9, true, FED_ROOT, PRED_HASH, sp1Proof);
    }

    // ─── Proof Failure ──────────────────────────────────────────────────────

    function test_mintRevertsOnInvalidProof() public {
        verifier.setShouldPass(false);
        bytes32 nullifier = keccak256("failMint");
        bytes memory sp1Proof = abi.encode(hex"0bad", abi.encode(true, FED_ROOT, PRED_HASH, nullifier));

        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.ProofVerificationFailed.selector);
        gate.mintWithCredential(99, FED_ROOT, PRED_HASH, sp1Proof);
    }

    // ─── Fail-Closed Verifier (codeless address must never accept) ──────────

    function test_constructorRejectsCodelessVerifier() public {
        address codeless = address(0x5678);
        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        new DreggCredentialGate(codeless, PROGRAM_VKEY, admin);
    }

    function test_verifyCredentialRevertsWhenVerifierLosesCode() public {
        bytes memory sp1Proof = abi.encode(
            hex"1234",
            abi.encode(true, FED_ROOT, PRED_HASH, keccak256("codelessNull"))
        );

        // Strip the verifier's code: the raw staticcall would now succeed
        // vacuously, so the call-time guard must reject.
        vm.etch(address(verifier), "");

        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        gate.verifyCredential(FED_ROOT, PRED_HASH, sp1Proof);
    }

    function test_mintRevertsWhenVerifierLosesCode() public {
        bytes memory sp1Proof = abi.encode(
            hex"1234",
            abi.encode(true, FED_ROOT, PRED_HASH, keccak256("codelessMint"))
        );

        vm.etch(address(verifier), "");

        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        gate.mintWithCredential(77, FED_ROOT, PRED_HASH, sp1Proof);
    }

    function test_voteRevertsWhenVerifierLosesCode() public {
        bytes memory sp1Proof = abi.encode(
            hex"1234",
            abi.encode(true, FED_ROOT, PRED_HASH, keccak256("codelessVote"))
        );

        vm.etch(address(verifier), "");

        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        gate.voteWithCredential(3, true, FED_ROOT, PRED_HASH, sp1Proof);
    }

    // ─── Two-Step Admin Rotation ────────────────────────────────────────────

    function test_adminRotationTwoStep() public {
        address newAdmin = address(0xAD31);

        gate.proposeAdmin(newAdmin);
        assertEq(gate.pendingAdmin(), newAdmin);
        assertEq(gate.admin(), admin); // proposal alone does NOT rotate

        vm.prank(newAdmin);
        gate.acceptAdmin();
        assertEq(gate.admin(), newAdmin);
        assertEq(gate.pendingAdmin(), address(0));

        // New admin holds the power...
        bytes32 newRoot = bytes32(uint256(0x1111));
        vm.prank(newAdmin);
        gate.setFederationTrust(newRoot, true);
        assertTrue(gate.trustedFederations(newRoot));

        // ...and the old admin has lost it.
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.setFederationTrust(newRoot, false);
    }

    function test_proposeAdminRejectsNonAdmin() public {
        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.proposeAdmin(user);
    }

    function test_acceptAdminRejectsNonPending() public {
        gate.proposeAdmin(address(0xAD31));

        vm.prank(user); // not the proposed admin
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.acceptAdmin();
    }

    function test_acceptAdminRejectsWhenNothingProposed() public {
        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.acceptAdmin();
    }
}
