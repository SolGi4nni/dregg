// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/launchpad/DreggDeployerGate.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {IDeployerGate} from "../contracts/launchpad/IDeployerGate.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";

/// #10 — the conduct bond is now ESCROWED over the launch + challenge window. A
/// deployer can no longer post a bond, register a launch through the BOND arm, and
/// reclaim the bond the next block (a rug with zero at stake). Driven through the
/// REAL `DreggLaunchpad.registerLaunch` → `authorizeDeploy` bond arm.
contract DreggDeployerGateBondEscrowTest is Test {
    DreggDeployerGate gate;
    DreggLaunchpad pad;

    address admin = address(0xA11CE);
    address deployer = address(0xBEEF);
    address griefer = address(0xBAD);

    uint256 constant MIN_BOND = 10 ether;

    function setUp() public {
        vm.prank(admin);
        gate = new DreggDeployerGate(admin, MIN_BOND);
        pad = new DreggLaunchpad(IDeployerGate(address(gate)));

        vm.startPrank(admin);
        gate.setAcceptedArms(uint8(0x0F)); // enable the bond arm (and the rest)
        gate.setLaunchpad(address(pad)); // pin the launchpad — non-griefable escrow
        vm.stopPrank();
    }

    function _schedule() internal pure returns (DreggLaunchpad.Schedule memory s) {
        s = DreggLaunchpad.Schedule({
            totalSupply: 1000,
            saleSupply: 600,
            creatorAllocation: 300,
            poolAllocation: 100,
            creatorLockUntil: 0,
            reservePrice: 1,
            graduationBps: 2000
        });
    }

    function _bondCap() internal view returns (bytes memory) {
        return abi.encode(gate.ARM_BOND(), bytes(""));
    }

    /// The real launchpad flow: `registerLaunch` calls `authorizeDeploy` with the
    /// bond capability, which escrow-locks the deployer's bond.
    function _registerLaunch() internal returns (uint256 id) {
        // Build args (incl. the cap's `ARM_BOND()` view call) BEFORE pranking, so
        // the external view does not consume the prank meant for registerLaunch.
        DreggLaunchpad.Schedule memory s = _schedule();
        bytes memory cap = _bondCap();
        vm.prank(deployer);
        id = pad.registerLaunch(
            "DreggMeme",
            "DMEME",
            s,
            100,
            100,
            ILaunchEligibility(address(0)),
            IClearingAttestor(address(0)),
            cap
        );
    }

    // ─── the flagship: post → register → withdraw is REFUSED, then allowed ─────

    function test_registerLaunchLocksBond_withdrawRefusedThenAllowed() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 50 ether}();

        // Backing a launch escrow-locks the bond for the challenge window.
        _registerLaunch();
        uint256 lockedUntil = gate.bondLockedUntil(deployer);
        assertEq(lockedUntil, block.timestamp + gate.CHALLENGE_WINDOW(), "locked for the challenge window");

        // While the launch is live / within the window, withdrawing REVERTS —
        // the rug-with-zero-bond hole is closed.
        vm.prank(deployer);
        vm.expectRevert(abi.encodeWithSelector(DreggDeployerGate.BondLocked.selector, lockedUntil));
        gate.withdrawBond();

        // Still locked one second before the window ends.
        vm.warp(lockedUntil - 1);
        vm.prank(deployer);
        vm.expectRevert(abi.encodeWithSelector(DreggDeployerGate.BondLocked.selector, lockedUntil));
        gate.withdrawBond();

        // At/after the window, with no live backed launch, withdraw SUCCEEDS.
        vm.warp(lockedUntil);
        uint256 balBefore = deployer.balance;
        vm.prank(deployer);
        gate.withdrawBond();
        assertEq(deployer.balance, balBefore + 50 ether, "bond returned after the window");
        assertEq(gate.bondOf(deployer), 0);
    }

    /// The escrow keeps the bond SLASHABLE the whole time — that is the point of
    /// holding it. A fraud proof can still slash a locked bond.
    function test_slashWorksWhileBondLocked() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 50 ether}();
        _registerLaunch();

        vm.prank(admin); // admin is the default slasher
        gate.slash(deployer, 20 ether, address(0xF00D));
        assertEq(gate.bondOf(deployer), 30 ether, "locked bond is still slashable");
        assertEq(address(0xF00D).balance, 20 ether);
    }

    /// A second backed launch pushes the lock further out (never shortens it).
    function test_secondLaunchExtendsTheLock() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 50 ether}();

        _registerLaunch();
        uint256 firstLock = gate.bondLockedUntil(deployer);

        vm.warp(block.timestamp + 10 days);
        _registerLaunch();
        uint256 secondLock = gate.bondLockedUntil(deployer);

        assertGt(secondLock, firstLock, "the lock extends, never retreats");
        assertEq(secondLock, block.timestamp + gate.CHALLENGE_WINDOW());
    }

    /// Once the launchpad is pinned, an arbitrary caller cannot drive
    /// `authorizeDeploy` — so it cannot grief the escrow by locking a bonded
    /// deployer's funds, nor snipe a pending launch's authorization.
    function test_pinnedLaunchpadBlocksDirectAuthorize() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 50 ether}();

        // Build the cap before arming the prank/expectRevert (its `ARM_BOND()`
        // view call would otherwise consume them).
        bytes memory cap = _bondCap();
        vm.prank(griefer);
        vm.expectRevert(DreggDeployerGate.Unauthorized.selector);
        gate.authorizeDeploy(deployer, keccak256("griefed-launch"), cap);

        // The deployer's bond was never locked by the griefer.
        assertEq(gate.bondLockedUntil(deployer), 0);
    }

    /// A deployer who never backed a launch is unaffected — withdraw stays free
    /// (the escrow gates only bonds that are actually backing something).
    function test_unbackedBondWithdrawsFreely() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 10 ether}();

        vm.prank(deployer);
        gate.withdrawBond();
        assertEq(gate.bondOf(deployer), 0);
    }
}
