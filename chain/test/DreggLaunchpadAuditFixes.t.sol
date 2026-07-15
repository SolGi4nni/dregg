// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";
import {IDeployerGate} from "../contracts/launchpad/IDeployerGate.sol";

/// Exploit-then-confirm tests for the independent codex audit (docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md).
/// Each test FAILS on the pre-fix contract and PASSES on the fixed one.
contract DreggLaunchpadAuditFixesTest is Test {
    DreggLaunchpad pad;

    address creator = makeAddr("creator");
    address alice = makeAddr("alice");
    address bob = makeAddr("bob");
    address carol = makeAddr("carol"); // the committed-but-never-revealed bidder

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

    function _register() internal returns (uint256 id) {
        vm.prank(creator);
        id = pad.registerLaunch(
            "DreggMeme",
            "DMEME",
            _schedule(),
            COMMIT_DUR,
            REVEAL_DUR,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            ""
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

    /// FINDING (stuck funds): a bidder who commits (escrows ETH) but never reveals is
    /// permanently locked OUT of their escrow once the launch CLEARS — settleBid
    /// requires `revealed`, reclaimEscrow refuses a `Cleared` launch. The intent
    /// (mirrored by test_RefundWorksForCommittedButNeverRevealed for the STALLED path)
    /// is that an unrevealed committer always recovers their deposit. This test proves
    /// carol recovers her full escrow after a cleared launch.
    function test_UnrevealedCommitterRecoversAfterClearing() public {
        uint256 id = _register();
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 3 * G, 400, keccak256("b"));
        // carol commits real ETH but will NEVER reveal.
        uint256 carolEscrow = 4 * G * 400;
        _commit(id, carol, 4 * G, 400, keccak256("c"));

        vm.warp(block.timestamp + COMMIT_DUR);
        _reveal(id, alice, 5 * G, 400, keccak256("a"));
        _reveal(id, bob, 3 * G, 400, keccak256("b"));
        // carol does NOT reveal.

        // The launch clears normally over the two revealed bids (indices 0,1).
        vm.warp(block.timestamp + REVEAL_DUR);
        uint256[] memory order = new uint256[](2);
        order[0] = 0; // alice (5G)
        order[1] = 1; // bob (3G)
        pad.finalizeClearing(id, order, "");
        assertEq(uint256(pad.phaseOf(id)), uint256(DreggLaunchpad.Phase.Cleared), "launch cleared");

        // carol's escrow is still held by the launchpad.
        (, bool revealed,,,,, uint256 deposit) = pad.getBid(id, carol);
        assertFalse(revealed, "carol never revealed");
        assertEq(deposit, carolEscrow, "carol's escrow is still escrowed");

        // THE FIX: settleBid fully refunds a committed-but-unrevealed bidder (filled=0).
        uint256 before = carol.balance;
        pad.settleBid(id, carol);
        assertEq(carol.balance - before, carolEscrow, "unrevealed committer recovers full escrow after clearing");

        // No double-recovery.
        vm.expectRevert(DreggLaunchpad.NothingToSettle.selector);
        pad.settleBid(id, carol);
    }
}
