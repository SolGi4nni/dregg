// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";
import {IDeployerGate} from "../contracts/launchpad/IDeployerGate.sol";

/// A never-attesting attestor: `attestClearing` always returns false. Stands in for
/// a dead devnet / a committee that never returns — the launch cannot finalize and
/// must fall through to the timeout-refund backstop.
contract DeadAttestor is IClearingAttestor {
    function attestClearing(uint256, uint256, uint256, bytes32, bytes calldata) external pure returns (bool) {
        return false;
    }
}

/// The liveness backstop (`reclaimEscrow`): a stuck / un-finalized clearing always
/// lets every participant reclaim the FULL escrow — permissionlessly, no operator —
/// so the worst case is stall-then-refund, NEVER loss.
/// (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md` §4.1, §5 shielded-grade backstop.)
contract DreggLaunchpadRefundTest is Test {
    DreggLaunchpad pad;

    address creator = makeAddr("creator");
    address alice = makeAddr("alice");
    address bob = makeAddr("bob");
    address carol = makeAddr("carol");

    uint64 constant COMMIT_DUR = 100;
    uint64 constant REVEAL_DUR = 100;
    uint256 constant G = 1e9;

    function setUp() public {
        pad = new DreggLaunchpad(IDeployerGate(address(0))); // permissionless deploy
        vm.deal(creator, 1 ether);
        vm.deal(alice, 1 ether);
        vm.deal(bob, 1 ether);
        vm.deal(carol, 1 ether);
    }

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

    function _register(IClearingAttestor att) internal returns (uint256 id) {
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

    function _reveal(uint256 id, address who, uint256 price, uint256 qty, bytes32 salt) internal {
        vm.prank(who);
        pad.revealBid(id, price, qty, salt);
    }

    // ── (i) refund AFTER timeout succeeds + returns EXACTLY the escrow ───────────

    function test_RefundAfterTimeoutReturnsExactEscrow() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a")); // escrow = 2000 gwei
        _commit(id, bob, 3 * G, 400, keccak256("b")); // escrow = 1200 gwei
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400, keccak256("a"));
        _reveal(id, bob, 3 * G, 400, keccak256("b"));

        // The reveal window closes, but NOBODY finalizes (dregg stalled). Past the
        // grace, the launch is stuck and refundable.
        vm.warp(block.timestamp + REVEAL_DUR); // == revealEnd
        assertFalse(pad.refundable(id), "not yet refundable at revealEnd");
        vm.warp(block.timestamp + pad.REFUND_GRACE());
        assertTrue(pad.refundable(id), "refundable past revealEnd + grace");

        uint256 aliceEscrow = 5 * G * 400;
        uint256 bobEscrow = 3 * G * 400;
        uint256 aBefore = alice.balance;
        uint256 bBefore = bob.balance;

        // Permissionless: anyone can trigger, but the ETH goes to the bidder. Each
        // reclaims via their own call (msg.sender is the payee).
        vm.prank(alice);
        pad.reclaimEscrow(id);
        vm.prank(bob);
        pad.reclaimEscrow(id);

        assertEq(alice.balance - aBefore, aliceEscrow, "alice reclaimed EXACTLY her escrow");
        assertEq(bob.balance - bBefore, bobEscrow, "bob reclaimed EXACTLY his escrow");
        // The launchpad no longer holds the escrow.
        assertEq(address(pad).balance, 0, "all escrow returned; launchpad drained to zero");
    }

    /// A committed-but-NEVER-REVEALED bidder (the launch died in the commit phase)
    /// still reclaims their full escrow.
    function test_RefundWorksForCommittedButNeverRevealed() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        // No reveals at all — launch stalls in Commit phase.
        vm.warp(block.timestamp + COMMIT_DUR + REVEAL_DUR + pad.REFUND_GRACE());

        uint256 escrow = 5 * G * 400;
        uint256 before = alice.balance;
        vm.prank(alice);
        pad.reclaimEscrow(id);
        assertEq(alice.balance - before, escrow, "unrevealed committer still reclaims full escrow");
    }

    // ── (ii) refund BEFORE timeout reverts ──────────────────────────────────────

    function test_RefundBeforeTimeoutReverts() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));

        // During commit — too early.
        vm.prank(alice);
        vm.expectPartialRevert(DreggLaunchpad.RefundNotYetAvailable.selector);
        pad.reclaimEscrow(id);

        // During reveal — still too early.
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400, keccak256("a"));
        vm.prank(alice);
        vm.expectPartialRevert(DreggLaunchpad.RefundNotYetAvailable.selector);
        pad.reclaimEscrow(id);

        // Reveal window closed but still WITHIN the clearing grace — too early.
        vm.warp(block.timestamp + REVEAL_DUR);
        vm.prank(alice);
        vm.expectPartialRevert(DreggLaunchpad.RefundNotYetAvailable.selector);
        pad.reclaimEscrow(id);
    }

    // ── (iii) no double refund ───────────────────────────────────────────────────

    function test_NoDoubleRefund() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        vm.warp(block.timestamp + COMMIT_DUR + REVEAL_DUR + pad.REFUND_GRACE());

        vm.prank(alice);
        pad.reclaimEscrow(id);
        // Second attempt reverts — the escrow is zeroed + latched.
        vm.prank(alice);
        vm.expectRevert(DreggLaunchpad.AlreadyRefunded.selector);
        pad.reclaimEscrow(id);
    }

    /// A wallet that never committed has nothing to reclaim.
    function test_NothingToRefundForNonBidder() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        vm.warp(block.timestamp + COMMIT_DUR + REVEAL_DUR + pad.REFUND_GRACE());
        vm.prank(carol); // never committed
        vm.expectRevert(DreggLaunchpad.NothingToRefund.selector);
        pad.reclaimEscrow(id);
    }

    // ── (iv) refund after a FAILED finalize (attestor never attests) ────────────

    function test_RefundAfterFailedFinalize() public {
        // A launch pinned to a dead attestor: finalize can never succeed.
        DeadAttestor dead = new DeadAttestor();
        uint256 id = _register(IClearingAttestor(address(dead)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400, keccak256("a"));
        _reveal(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + REVEAL_DUR);

        // finalize attempts FAIL (attestor returns false) — the launch stays pre-final.
        uint256[] memory order = new uint256[](2);
        order[0] = 0;
        order[1] = 1;
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, order, hex"dead");
        assertEq(uint256(pad.phaseOf(id)), uint256(DreggLaunchpad.Phase.Reveal), "stays in Reveal after failed finalize");

        // Past the grace: refunds open, everyone recovers their escrow.
        vm.warp(block.timestamp + pad.REFUND_GRACE());
        uint256 aBefore = alice.balance;
        vm.prank(alice);
        pad.reclaimEscrow(id);
        assertEq(alice.balance - aBefore, 5 * G * 400, "refund after a failed finalize");
    }

    // ── (v) a FINALIZED launch cannot be refund-drained ─────────────────────────

    function test_FinalizedLaunchCannotBeRefundDrained() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400, keccak256("a"));
        _reveal(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + REVEAL_DUR);
        uint256[] memory order = new uint256[](2);
        order[0] = 0; // alice (5)
        order[1] = 1; // bob (3)
        pad.finalizeClearing(id, order, ""); // clears — no attestor pinned

        // Even far past the grace, a cleared launch is NOT refundable: settle is the
        // path. A refund door here would double-pay a winner (drain).
        vm.warp(block.timestamp + pad.REFUND_GRACE() + 1);
        assertFalse(pad.refundable(id), "cleared launch is never refundable");
        vm.prank(alice);
        vm.expectRevert(DreggLaunchpad.LaunchAlreadyCleared.selector);
        pad.reclaimEscrow(id);

        // The honest path still works: alice settles (pays uniform price, refunded the rest).
        uint256 before = alice.balance;
        pad.settleBid(id, alice);
        // clearing price = bob's 3 gwei; alice filled 400 → pays 1200 gwei, escrow 2000 → refund 800.
        assertEq(alice.balance - before, (5 * G - 3 * G) * 400, "settle refunds deposit - uniform payment");
    }

    // ── (vi) the refund path cannot ESCAPE a valid clearing ─────────────────────

    /// Within the clearing window a bidder cannot pre-empt a valid finalize with a
    /// refund (too early), AND once cleared the refund is permanently closed — so a
    /// bidder who dislikes their fill cannot bail out of a valid clearing.
    function test_RefundCannotEscapeValidClearing() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400, keccak256("a"));
        _reveal(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + REVEAL_DUR);

        // A losing/partial bidder tries to refund instead of accepting the clearing:
        // too early (still in the clearing window).
        vm.prank(alice);
        vm.expectPartialRevert(DreggLaunchpad.RefundNotYetAvailable.selector);
        pad.reclaimEscrow(id);

        // The clearing lands validly.
        uint256[] memory order = new uint256[](2);
        order[0] = 0;
        order[1] = 1;
        pad.finalizeClearing(id, order, "");

        // Now, even past the grace, no escape hatch: cleared ⇒ not refundable.
        vm.warp(block.timestamp + pad.REFUND_GRACE() + 1);
        vm.prank(alice);
        vm.expectRevert(DreggLaunchpad.LaunchAlreadyCleared.selector);
        pad.reclaimEscrow(id);
    }

    /// The dual guard: once the grace elapses, a STALE finalize is refused — a
    /// straggler operator cannot re-open a launch that has entered its refund window
    /// and override refunds. Clearing and refund windows are strictly disjoint.
    function test_StaleFinalizeRefusedAfterGrace() public {
        uint256 id = _register(IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400, keccak256("a"));
        _reveal(id, bob, 3 * G, 400, keccak256("b"));
        vm.warp(block.timestamp + REVEAL_DUR + pad.REFUND_GRACE());

        uint256[] memory order = new uint256[](2);
        order[0] = 0;
        order[1] = 1;
        vm.expectPartialRevert(DreggLaunchpad.ClearingWindowClosed.selector);
        pad.finalizeClearing(id, order, "");
    }
}
