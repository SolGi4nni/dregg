// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";
import {CommitteeAttestor} from "../contracts/launchpad/CommitteeAttestor.sol";

/// The v1 committee-signature attestor (the PROVED-grade trust anchor) + its
/// fraud-proof/challenge backstop. Adversarial: a valid quorum attests and the
/// launch clears; a forged / insufficient / wrong-tuple sig is REJECTED (→ the
/// launch stays pre-final, refundable via the timeout backstop); a lying committee
/// is SLASHED by an on-chain fraud proof and an honest one CANNOT be.
/// (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §3.4, §3.6.)
contract DreggLaunchpadCommitteeAttestorTest is Test {
    DreggLaunchpad pad;
    CommitteeAttestor att;

    // Committee of 3, quorum 2 (a single rogue signer is insufficient).
    uint256 constant PK1 = 0xA11CE;
    uint256 constant PK2 = 0xB0B;
    uint256 constant PK3 = 0xCACA0;
    uint256 constant PK_ROGUE = 0xDEAD; // a non-committee key

    address creator = makeAddr("creator");
    address alice = makeAddr("alice");
    address bob = makeAddr("bob");

    uint64 constant COMMIT_DUR = 100;
    uint64 constant REVEAL_DUR = 100;
    uint256 constant G = 1e9;

    function setUp() public {
        pad = new DreggLaunchpad();
        address[] memory signers = new address[](3);
        signers[0] = vm.addr(PK1);
        signers[1] = vm.addr(PK2);
        signers[2] = vm.addr(PK3);
        att = new CommitteeAttestor(signers, 2);

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

    function _register(IClearingAttestor a) internal returns (uint256 id) {
        vm.prank(creator);
        id = pad.registerLaunch("DreggMeme", "DMEME", _schedule(), COMMIT_DUR, REVEAL_DUR, ILaunchEligibility(address(0)), a);
    }

    function _commit(uint256 id, address who, uint256 price, uint256 qty, bytes32 salt) internal {
        bytes32 seal = pad.sealOf(price, qty, salt, who);
        vm.prank(who);
        pad.commitBid{value: price * qty}(id, seal, "");
    }

    /// Build a quorum proof: sign `digest` with each pk, sorted ASCENDING by signer
    /// address (the attestor's dedup discipline), packed as `abi.encode(bytes[])`.
    function _proof(uint256[] memory pks, bytes32 digest) internal returns (bytes memory) {
        // insertion sort by signer address
        for (uint256 i = 1; i < pks.length; i++) {
            uint256 key = pks[i];
            address ka = vm.addr(key);
            uint256 j = i;
            while (j > 0 && vm.addr(pks[j - 1]) > ka) {
                pks[j] = pks[j - 1];
                j--;
            }
            pks[j] = key;
        }
        bytes[] memory sigs = new bytes[](pks.length);
        for (uint256 i = 0; i < pks.length; i++) {
            (uint8 v, bytes32 r, bytes32 s) = vm.sign(pks[i], digest);
            sigs[i] = abi.encodePacked(r, s, v);
        }
        return abi.encode(sigs);
    }

    /// The launchpad's book-commit fold (mirrors `_runClearing:373`) for parallel
    /// (bidder, price, qty) arrays in clearing order.
    function _fold(address[] memory b, uint256[] memory p, uint256[] memory q) internal pure returns (bytes32 acc) {
        for (uint256 i = 0; i < b.length; i++) {
            acc = keccak256(abi.encodePacked(acc, b[i], p[i], q[i]));
        }
    }

    /// Two revealed bidders alice(5G,400)=index0, bob(3G,400)=index1, ready to clear.
    function _setupTwoRevealed(uint256 id) internal {
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(alice);
        pad.revealBid(id, 5 * G, 400, keccak256("a")); // index 0
        vm.prank(bob);
        pad.revealBid(id, 3 * G, 400, keccak256("b")); // index 1
        vm.warp(block.timestamp + REVEAL_DUR);
    }

    /// bookCommit for the standard two-bidder clear in order [alice, bob].
    function _twoBidderBookCommit() internal view returns (bytes32) {
        address[] memory b = new address[](2);
        uint256[] memory p = new uint256[](2);
        uint256[] memory q = new uint256[](2);
        b[0] = alice;
        p[0] = 5 * G;
        q[0] = 400;
        b[1] = bob;
        p[1] = 3 * G;
        q[1] = 400;
        return _fold(b, p, q);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (1) VALID k-of-n quorum → attestClearing true → finalizeClearing proceeds
    // ══════════════════════════════════════════════════════════════════════════

    function test_ValidQuorumAttestsAndClears() public {
        uint256 id = _register(att);
        _setupTwoRevealed(id);

        // Undersubscribed (800 < 1000): both win, uniform price = bob's 3 gwei.
        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(id, 1000, 3 * G, bookCommit);

        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK2;
        bytes memory proof = _proof(pks, digest);

        // Sanity: the attestor accepts the quorum directly.
        assertTrue(att.attestClearing(id, 1000, 3 * G, bookCommit, proof), "2-of-3 quorum attests");

        uint256[] memory order = new uint256[](2);
        order[0] = 0; // alice
        order[1] = 1; // bob
        pad.finalizeClearing(id, order, proof);
        assertTrue(pad.clearingAttested(id), "committee-attested clearing recorded (PROVED rung)");
        assertEq(pad.clearingPriceOf(id), 3 * G, "uniform price = lowest winner (bob)");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (2) INSUFFICIENT / FORGED / ROGUE → false → launch stays pre-final, refundable
    // ══════════════════════════════════════════════════════════════════════════

    /// A single rogue signer (1-of-3 with a quorum of 2) cannot attest.
    function test_SingleSignerBelowQuorumRejected() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(1, 1000, 3 * G, bookCommit);
        uint256[] memory pks = new uint256[](1);
        pks[0] = PK1;
        assertFalse(att.attestClearing(1, 1000, 3 * G, bookCommit, _proof(pks, digest)), "1-of-3 is below quorum");
    }

    /// A forged signature from a NON-committee key does not count toward quorum.
    function test_ForgedNonCommitteeSignatureRejected() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(1, 1000, 3 * G, bookCommit);
        // One real committee sig + one forged (rogue) sig = still only 1 valid.
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK_ROGUE;
        assertFalse(att.attestClearing(1, 1000, 3 * G, bookCommit, _proof(pks, digest)), "forged sig does not count");
    }

    /// A single rogue signer cannot inflate itself to a quorum by repeating its sig.
    function test_DuplicatedSignerCannotReachQuorum() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(1, 1000, 3 * G, bookCommit);
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(PK1, digest);
        bytes memory sig = abi.encodePacked(r, s, v);
        bytes[] memory sigs = new bytes[](2);
        sigs[0] = sig;
        sigs[1] = sig; // same signer twice — not strictly ascending, counts once
        assertFalse(att.attestClearing(1, 1000, 3 * G, bookCommit, abi.encode(sigs)), "duplicate sig counts once");
    }

    /// A garbage proof blob returns false (never reverts) — the launch stays pre-final.
    function test_MalformedProofReturnsFalse() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        assertFalse(att.attestClearing(1, 1000, 3 * G, bookCommit, hex"deadbeef"), "malformed proof yields false");
    }

    /// The integration: an insufficient sig blocks finalize (`ClearingNotAttested`),
    /// the launch stays in Reveal, and every bidder recovers escrow via the timeout
    /// backstop — a corrupt/withholding committee is a liveness fault, never a loss.
    function test_InsufficientSigBlocksFinalizeThenRefundable() public {
        uint256 id = _register(att);
        _setupTwoRevealed(id);

        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(id, 1000, 3 * G, bookCommit);
        uint256[] memory pks = new uint256[](1);
        pks[0] = PK1; // only 1-of-2
        bytes memory weak = _proof(pks, digest);

        uint256[] memory order = new uint256[](2);
        order[0] = 0;
        order[1] = 1;
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, order, weak);
        assertEq(uint256(pad.phaseOf(id)), uint256(DreggLaunchpad.Phase.Reveal), "stays pre-final");

        // Timeout backstop returns the escrow.
        vm.warp(block.timestamp + pad.REFUND_GRACE());
        uint256 before = alice.balance;
        vm.prank(alice);
        pad.reclaimEscrow(id);
        assertEq(alice.balance - before, 5 * G * 400, "escrow reclaimed after a withholding committee");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (3) WRONG TUPLE — a quorum over a DIFFERENT tuple does not attest this one
    // ══════════════════════════════════════════════════════════════════════════

    /// The committee signs one bookCommit; a clearing presenting a DIFFERENT
    /// bookCommit is not attested (the digest, hence the recovered signers, differ).
    function test_WrongBookCommitRejected() public {
        bytes32 signedBook = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(1, 1000, 3 * G, signedBook);
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK2;
        bytes memory proof = _proof(pks, digest);

        // Present a different bookCommit with the same signatures → false.
        bytes32 tampered = keccak256("a different book");
        assertFalse(att.attestClearing(1, 1000, 3 * G, tampered, proof), "sig over another book does not attest this one");
        // And the honestly-signed one still verifies (control).
        assertTrue(att.attestClearing(1, 1000, 3 * G, signedBook, proof), "the signed book verifies");
    }

    /// Same for a tampered clearingPrice in the tuple.
    function test_WrongClearingPriceRejected() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(1, 1000, 3 * G, bookCommit);
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK2;
        bytes memory proof = _proof(pks, digest);
        assertFalse(att.attestClearing(1, 1000, 4 * G, bookCommit, proof), "sig over price 3G does not attest 4G");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (4) THE FRAUD-PROOF / CHALLENGE HOOK — a lying committee is SLASHED
    // ══════════════════════════════════════════════════════════════════════════

    /// Arm (b): the committee signs a clearingPrice that is NOT the marginal price of
    /// the book it committed to. A challenge recomputes the canonical clearing and
    /// proves the lie → the committee is slashed.
    function test_FraudProof_WrongPriceSlashesCommittee() public {
        // Book in canonical descending order; true marginal @ saleSupply 1000,
        // reserve 1G is bob's 3G. The committee LIES and signs 5G.
        bytes32 bookCommit = _twoBidderBookCommit();
        uint256 lyingPrice = 5 * G;
        bytes32 digest = att.attestationDigest(7, 1000, lyingPrice, bookCommit);
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK2;
        bytes memory proof = _proof(pks, digest);

        CommitteeAttestor.BookEntry[] memory book = new CommitteeAttestor.BookEntry[](2);
        book[0] = CommitteeAttestor.BookEntry(alice, 5 * G, 400);
        book[1] = CommitteeAttestor.BookEntry(bob, 3 * G, 400);

        att.challengeAttestation(7, 1000, lyingPrice, bookCommit, 1 * G, proof, book);
        assertTrue(att.slashed(), "lying committee slashed");
        assertTrue(att.fraudProven(digest), "the fraudulent digest is recorded");

        // A slashed committee can no longer attest anything — even a truthful tuple.
        bytes32 honestDigest = att.attestationDigest(7, 1000, 3 * G, bookCommit);
        bytes memory honestProof = _proof(pks, honestDigest);
        assertFalse(att.attestClearing(7, 1000, 3 * G, bookCommit, honestProof), "slashed committee attests nothing");
    }

    /// Arm (a), unconditional: the committee attests a NON-DESCENDING clearing order.
    /// The order alone is non-canonical → fraud, no reservePrice assumption needed.
    function test_FraudProof_NonDescendingOrderSlashesCommittee() public {
        // A non-descending committed order: bob(3G) BEFORE alice(5G).
        address[] memory b = new address[](2);
        uint256[] memory p = new uint256[](2);
        uint256[] memory q = new uint256[](2);
        b[0] = bob;
        p[0] = 3 * G;
        q[0] = 400;
        b[1] = alice;
        p[1] = 5 * G;
        q[1] = 400;
        bytes32 bookCommit = _fold(b, p, q);

        bytes32 digest = att.attestationDigest(9, 1000, 3 * G, bookCommit);
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK3;
        bytes memory proof = _proof(pks, digest);

        CommitteeAttestor.BookEntry[] memory book = new CommitteeAttestor.BookEntry[](2);
        book[0] = CommitteeAttestor.BookEntry(bob, 3 * G, 400);
        book[1] = CommitteeAttestor.BookEntry(alice, 5 * G, 400);

        // reservePrice irrelevant for arm (a).
        att.challengeAttestation(9, 1000, 3 * G, bookCommit, 0, proof, book);
        assertTrue(att.slashed(), "non-descending order slashes the committee");
    }

    /// NO FALSE POSITIVES: an HONEST attestation (correct descending order + correct
    /// marginal price) cannot be slashed.
    function test_FraudProof_HonestAttestationCannotBeSlashed() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        uint256 honestPrice = 3 * G; // the true marginal @ 1000/reserve 1G
        bytes32 digest = att.attestationDigest(11, 1000, honestPrice, bookCommit);
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK2;
        bytes memory proof = _proof(pks, digest);

        CommitteeAttestor.BookEntry[] memory book = new CommitteeAttestor.BookEntry[](2);
        book[0] = CommitteeAttestor.BookEntry(alice, 5 * G, 400);
        book[1] = CommitteeAttestor.BookEntry(bob, 3 * G, 400);

        vm.expectRevert(CommitteeAttestor.NotFraudulent.selector);
        att.challengeAttestation(11, 1000, honestPrice, bookCommit, 1 * G, proof, book);
        assertFalse(att.slashed(), "an honest committee is NOT slashed");
    }

    /// A challenge cannot FRAME the committee with a fabricated book (one that does
    /// not fold to the attested bookCommit).
    function test_FraudProof_FabricatedBookRejected() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(13, 1000, 3 * G, bookCommit);
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK2;
        bytes memory proof = _proof(pks, digest);

        // A book that does NOT match bookCommit (different quantities).
        CommitteeAttestor.BookEntry[] memory fake = new CommitteeAttestor.BookEntry[](2);
        fake[0] = CommitteeAttestor.BookEntry(alice, 5 * G, 999);
        fake[1] = CommitteeAttestor.BookEntry(bob, 3 * G, 999);

        vm.expectPartialRevert(CommitteeAttestor.BookCommitMismatch.selector);
        att.challengeAttestation(13, 1000, 3 * G, bookCommit, 1 * G, proof, fake);
        assertFalse(att.slashed(), "cannot frame with a fabricated book");
    }

    /// A challenge over a tuple the committee NEVER attested (no quorum) is refused —
    /// you can only challenge a genuine, quorum-signed attestation.
    function test_FraudProof_UnattestedTupleRejected() public {
        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(15, 1000, 5 * G, bookCommit);
        uint256[] memory pks = new uint256[](1);
        pks[0] = PK1; // only 1-of-2 — never a quorum
        bytes memory weak = _proof(pks, digest);

        CommitteeAttestor.BookEntry[] memory book = new CommitteeAttestor.BookEntry[](2);
        book[0] = CommitteeAttestor.BookEntry(alice, 5 * G, 400);
        book[1] = CommitteeAttestor.BookEntry(bob, 3 * G, 400);

        vm.expectRevert(CommitteeAttestor.NotAttested.selector);
        att.challengeAttestation(15, 1000, 5 * G, bookCommit, 1 * G, weak, book);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // (5) HONEST BOUNDS — even a committee-attested clearing cannot over-mint /
    //     drain / charge above escrow (the guards hold regardless of the attestor).
    // ══════════════════════════════════════════════════════════════════════════

    function test_BoundsHoldUnderCommitteeAttestation() public {
        uint256 id = _register(att);
        _setupTwoRevealed(id);
        DreggLaunchToken tok = DreggLaunchToken(pad.tokenOf(id));
        uint256 supplyBefore = tok.totalSupply();

        bytes32 bookCommit = _twoBidderBookCommit();
        bytes32 digest = att.attestationDigest(id, 1000, 3 * G, bookCommit);
        uint256[] memory pks = new uint256[](2);
        pks[0] = PK1;
        pks[1] = PK2;
        bytes memory proof = _proof(pks, digest);

        uint256[] memory order = new uint256[](2);
        order[0] = 0;
        order[1] = 1;
        pad.finalizeClearing(id, order, proof);

        // Settle: payment is bounded by escrow; the refund is exact.
        uint256 aBefore = alice.balance;
        pad.settleBid(id, alice); // pays 3G*400, escrow 5G*400 → refund 2G*400
        assertEq(alice.balance - aBefore, (5 * G - 3 * G) * 400, "charged at most the escrow (uniform payment)");

        // No over-mint: total supply is fixed by the one-shot mint, attestor or not.
        assertEq(tok.totalSupply(), supplyBefore, "committee attestation cannot inflate supply");
    }

    // ── constructor guards ──────────────────────────────────────────────────────

    function test_ConstructorRejectsBadThreshold() public {
        address[] memory signers = new address[](2);
        signers[0] = vm.addr(PK1);
        signers[1] = vm.addr(PK2);
        vm.expectRevert(abi.encodeWithSelector(CommitteeAttestor.BadThreshold.selector, uint256(3), uint256(2)));
        new CommitteeAttestor(signers, 3); // threshold > n
    }

    function test_ConstructorRejectsDuplicateSigner() public {
        address[] memory signers = new address[](2);
        signers[0] = vm.addr(PK1);
        signers[1] = vm.addr(PK1);
        vm.expectRevert(abi.encodeWithSelector(CommitteeAttestor.DuplicateSigner.selector, vm.addr(PK1)));
        new CommitteeAttestor(signers, 1);
    }
}
