// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/launchpad/DreggDeployerGate.sol";

/// #11 — proofless slash. Before the fix, `slash` was `msg.sender == slasher`, any
/// amount, arbitrary recipient, NO on-chain fraud proof: a compromised OPERATIONAL
/// slasher key drained every bond in one call. Now the operational slasher must
/// TIMELOCK (propose → wait `SLASH_DELAY` → execute), and governance (`admin`) can
/// VETO within the window (and rotate the key). Governance keeps an immediate
/// `slash` — it is already the omnipotent root, so that grants it no new power.
contract DreggDeployerGateSlashTimelockTest is Test {
    DreggDeployerGate gate;

    address admin = address(0xA11CE);
    address slasher = address(0x5145E4); // the OPERATIONAL fraud-detection key
    address deployer = address(0xBEEF);
    address beneficiary = address(0xF00D);
    address stranger = address(0xBAD);

    uint256 constant MIN_BOND = 10 ether;

    function setUp() public {
        vm.prank(admin);
        gate = new DreggDeployerGate(admin, MIN_BOND);

        // Separate the operational slasher from governance (production posture).
        vm.prank(admin);
        gate.setSlasher(slasher);

        // A deployer stakes a bond.
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 50 ether}();
    }

    // ─── the hole is closed: the operational slasher cannot drain in one call ──

    /// The operational slasher has NO immediate slash — `slash` is governance-only.
    function test_operationalSlasherCannotImmediateSlash() public {
        vm.prank(slasher);
        vm.expectRevert(DreggDeployerGate.Unauthorized.selector);
        gate.slash(deployer, 50 ether, beneficiary);

        assertEq(gate.bondOf(deployer), 50 ether, "bond untouched");
    }

    /// A staged slash cannot execute before its timelock elapses.
    function test_executeBeforeEtaReverts() public {
        vm.prank(slasher);
        uint256 id = gate.proposeSlash(deployer, 20 ether, beneficiary);

        uint256 eta = block.timestamp + gate.SLASH_DELAY();
        vm.prank(slasher);
        vm.expectRevert(abi.encodeWithSelector(DreggDeployerGate.SlashNotReady.selector, eta));
        gate.executeSlash(id);

        assertEq(gate.bondOf(deployer), 50 ether, "bond untouched before eta");
    }

    /// A validly-timelocked slash succeeds once `eta` passes.
    function test_timelockedSlashSucceeds() public {
        vm.prank(slasher);
        uint256 id = gate.proposeSlash(deployer, 20 ether, beneficiary);

        vm.warp(block.timestamp + gate.SLASH_DELAY());
        vm.prank(slasher);
        gate.executeSlash(id);

        assertEq(gate.bondOf(deployer), 30 ether, "20 ether slashed");
        assertEq(beneficiary.balance, 20 ether, "slash paid to recipient");
    }

    /// Governance can VETO a staged slash before it executes (the compromised-key
    /// backstop): after a cancel, execute reverts.
    function test_governanceCancelVetoesSlash() public {
        vm.prank(slasher);
        uint256 id = gate.proposeSlash(deployer, 50 ether, stranger);

        // Governance notices the rogue proposal and cancels it within the window.
        vm.prank(admin);
        gate.cancelSlash(id);

        vm.warp(block.timestamp + gate.SLASH_DELAY());
        vm.prank(slasher);
        vm.expectRevert(abi.encodeWithSelector(DreggDeployerGate.SlashAlreadyResolved.selector, id));
        gate.executeSlash(id);

        assertEq(gate.bondOf(deployer), 50 ether, "bond fully intact after veto");
    }

    /// Only the operational slasher may stage a slash.
    function test_nonSlasherCannotPropose() public {
        vm.prank(stranger);
        vm.expectRevert(DreggDeployerGate.Unauthorized.selector);
        gate.proposeSlash(deployer, 1 ether, stranger);
    }

    /// Only governance may cancel a staged slash.
    function test_nonAdminCannotCancel() public {
        vm.prank(slasher);
        uint256 id = gate.proposeSlash(deployer, 20 ether, beneficiary);

        vm.prank(stranger);
        vm.expectRevert(DreggDeployerGate.Unauthorized.selector);
        gate.cancelSlash(id);
    }

    /// A staged slash cannot be executed twice.
    function test_doubleExecuteReverts() public {
        vm.prank(slasher);
        uint256 id = gate.proposeSlash(deployer, 20 ether, beneficiary);
        vm.warp(block.timestamp + gate.SLASH_DELAY());
        vm.prank(slasher);
        gate.executeSlash(id);

        vm.prank(slasher);
        vm.expectRevert(abi.encodeWithSelector(DreggDeployerGate.SlashAlreadyResolved.selector, id));
        gate.executeSlash(id);
    }

    /// Governance retains an immediate slash (already the omnipotent root).
    function test_governanceImmediateSlashStillWorks() public {
        vm.prank(admin);
        gate.slash(deployer, 15 ether, beneficiary);

        assertEq(gate.bondOf(deployer), 35 ether);
        assertEq(beneficiary.balance, 15 ether);
    }
}
