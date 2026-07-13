// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggVault.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {MockSP1Verifier, MockSettlement, MockERC20} from "./DreggVault.t.sol";

/// End-to-end exercise of the DreggVault TIMEOUT/REFUND ESCROW — the two-branch,
/// exactly-once state machine that makes locking into DrEX safe.
///
/// A locked escrow reaches EXACTLY ONE terminal state:
///   • RELEASED to the ring-matched recipient (a DrEX fill proof whose clearing
///     root is proven by the settlement contract), XOR
///   • REFUNDED to the depositor (the per-deposit deadline passed with no fill).
///
/// The teeth here are the mutual exclusion + idempotence: filled→release then
/// no-refund; unfilled→refund then no-release; early-refund reverts; proofless /
/// unproven-root release reverts; double-release / double-refund revert; the
/// released-and-also-refunded state is unreachable.
contract DreggVaultEscrowTest is Test {
    DreggVault public vault;
    MockSP1Verifier public verifier;
    MockSettlement public settlement;
    MockERC20 public token;

    bytes32 constant PROGRAM_VKEY = bytes32(uint256(0xdeadbeef));
    address constant RECIPIENT = address(0xBEEF); // the ring-matched recipient
    bytes32 constant CLEARING_ROOT = bytes32(uint256(0xC1EA5));

    function setUp() public {
        verifier = new MockSP1Verifier();
        settlement = new MockSettlement();
        vault = new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(address(settlement)));
        token = new MockERC20();
    }

    // ─── helpers ──────────────────────────────────────────────────────────────

    /// Build an SP1 fill-proof envelope naming `escrowId` as filled: release
    /// `amount` of `token` to `recipient` under `clearingRoot`.
    function _fillProof(
        bytes32 escrowId,
        address token_,
        uint256 amount,
        address recipient,
        bytes32 clearingRoot
    ) internal pure returns (bytes memory) {
        bytes memory publicValues =
            abi.encode(true, escrowId, token_, amount, recipient, clearingRoot);
        return abi.encode(hex"1234", publicValues);
    }

    function _lockETH(bytes32 escrowId, uint256 amount, uint256 deadline) internal {
        vault.escrowDepositETH{value: amount}(deadline, escrowId);
    }

    // ─── DEPOSIT (lock) ─────────────────────────────────────────────────────────

    function test_escrowDepositETH_locksAndAccounts() public {
        bytes32 id = keccak256("e1");
        uint256 deadline = block.timestamp + 1 days;
        _lockETH(id, 1 ether, deadline);

        (address t, address depositor, uint256 amount, uint256 dl, DreggVault.EscrowStatus status) =
            vault.escrows(id);
        assertEq(t, address(0));
        assertEq(depositor, address(this));
        assertEq(amount, 1 ether);
        assertEq(dl, deadline);
        assertEq(uint256(status), uint256(DreggVault.EscrowStatus.Locked));
        assertEq(vault.escrowedBalances(address(0)), 1 ether);
        // Escrow custody is DISJOINT from the generic note-mirror pool.
        assertEq(vault.tokenBalances(address(0)), 0);
    }

    function test_escrowDepositERC20_locks() public {
        bytes32 id = keccak256("e-erc20");
        token.mint(address(this), 5 ether);
        token.approve(address(vault), 5 ether);
        vault.escrowDeposit(address(token), 5 ether, block.timestamp + 1 days, id);

        assertEq(token.balanceOf(address(vault)), 5 ether);
        assertEq(vault.escrowedBalances(address(token)), 5 ether);
        assertEq(uint256(vault.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Locked));
    }

    function test_escrowDeposit_zeroAmountReverts() public {
        vm.expectRevert(DreggVault.ZeroAmount.selector);
        vault.escrowDepositETH{value: 0}(block.timestamp + 1 days, keccak256("z"));
    }

    function test_escrowDeposit_zeroDeadlineReverts() public {
        vm.expectRevert(DreggVault.ZeroDeadline.selector);
        vault.escrowDepositETH{value: 1 ether}(0, keccak256("zd"));
    }

    function test_escrowDeposit_duplicateIdReverts() public {
        bytes32 id = keccak256("dup");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        vm.expectRevert(abi.encodeWithSelector(DreggVault.DuplicateEscrowId.selector, id));
        vault.escrowDepositETH{value: 1 ether}(block.timestamp + 1 days, id);
    }

    // ─── POLARITY 1: FILLED → RELEASE (then cannot refund) ──────────────────────

    function test_filledEscrowReleasesToRecipient() public {
        bytes32 id = keccak256("fill");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);

        bytes memory proof = _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT);
        vault.escrowRelease(id, RECIPIENT, proof);

        assertEq(RECIPIENT.balance, 1 ether);
        assertEq(uint256(vault.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Released));
        assertEq(vault.escrowedBalances(address(0)), 0);
    }

    /// TOOTH: once Released, the escrow is terminal — a refund (even after the
    /// deadline) reverts. Released-and-also-refunded is unreachable.
    function test_releasedEscrowCannotBeRefunded() public {
        bytes32 id = keccak256("fill-then-refund");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);
        vault.escrowRelease(id, RECIPIENT, _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT));

        // Warp well past the deadline: still cannot refund a released escrow.
        vm.warp(block.timestamp + 30 days);
        vm.expectRevert(abi.encodeWithSelector(DreggVault.EscrowNotLocked.selector, id));
        vault.escrowRefund(id);
        // Recipient keeps the funds; depositor got nothing back.
        assertEq(RECIPIENT.balance, 1 ether);
    }

    function test_filledEscrowReleaseERC20() public {
        bytes32 id = keccak256("fill-erc20");
        token.mint(address(this), 3 ether);
        token.approve(address(vault), 3 ether);
        vault.escrowDeposit(address(token), 3 ether, block.timestamp + 1 days, id);
        settlement.setProven(CLEARING_ROOT, true);

        vault.escrowRelease(id, RECIPIENT, _fillProof(id, address(token), 3 ether, RECIPIENT, CLEARING_ROOT));
        assertEq(token.balanceOf(RECIPIENT), 3 ether);
        assertEq(vault.escrowedBalances(address(token)), 0);
    }

    // ─── POLARITY 2: UNFILLED → REFUND (then cannot release) ────────────────────

    function test_unfilledEscrowRefundsToDepositorAfterDeadline() public {
        bytes32 id = keccak256("nofill");
        uint256 deadline = block.timestamp + 1 days;
        _lockETH(id, 1 ether, deadline);

        uint256 balBefore = address(this).balance;
        vm.warp(deadline + 1);
        vault.escrowRefund(id);

        assertEq(address(this).balance, balBefore + 1 ether);
        assertEq(uint256(vault.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Refunded));
        assertEq(vault.escrowedBalances(address(0)), 0);
    }

    /// TOOTH: once Refunded, the escrow is terminal — a release (even with a valid
    /// fill proof over a proven root) reverts. Refunded-and-also-released is
    /// unreachable.
    function test_refundedEscrowCannotBeReleased() public {
        bytes32 id = keccak256("refund-then-fill");
        uint256 deadline = block.timestamp + 1 days;
        _lockETH(id, 1 ether, deadline);
        vm.warp(deadline + 1);
        vault.escrowRefund(id);

        settlement.setProven(CLEARING_ROOT, true);
        vm.expectRevert(abi.encodeWithSelector(DreggVault.EscrowNotLocked.selector, id));
        vault.escrowRelease(id, RECIPIENT, _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT));
        assertEq(RECIPIENT.balance, 0);
    }

    function test_unfilledEscrowRefundERC20() public {
        bytes32 id = keccak256("nofill-erc20");
        token.mint(address(this), 4 ether);
        token.approve(address(vault), 4 ether);
        uint256 deadline = block.timestamp + 1 days;
        vault.escrowDeposit(address(token), 4 ether, deadline, id);

        vm.warp(deadline + 1);
        vault.escrowRefund(id);
        assertEq(token.balanceOf(address(this)), 4 ether); // full amount back
        assertEq(vault.escrowedBalances(address(token)), 0);
    }

    // ─── REFUND guards ──────────────────────────────────────────────────────────

    /// TOOTH: a refund BEFORE the deadline reverts (the timeout IS the condition).
    function test_refundBeforeDeadlineReverts() public {
        bytes32 id = keccak256("early");
        uint256 deadline = block.timestamp + 1 days;
        _lockETH(id, 1 ether, deadline);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.RefundBeforeDeadline.selector, id, deadline, block.timestamp
            )
        );
        vault.escrowRefund(id);
    }

    /// At exactly `deadline` the refund is still too early (strict `>` semantics).
    function test_refundAtExactDeadlineReverts() public {
        bytes32 id = keccak256("exact");
        uint256 deadline = block.timestamp + 1 days;
        _lockETH(id, 1 ether, deadline);
        vm.warp(deadline); // block.timestamp == deadline
        vm.expectRevert(
            abi.encodeWithSelector(DreggVault.RefundBeforeDeadline.selector, id, deadline, deadline)
        );
        vault.escrowRefund(id);
    }

    function test_refundByNonDepositorReverts() public {
        bytes32 id = keccak256("wrongcaller");
        uint256 deadline = block.timestamp + 1 days;
        _lockETH(id, 1 ether, deadline);
        vm.warp(deadline + 1);

        address stranger = address(0x5715A9E5);
        vm.prank(stranger);
        vm.expectRevert(
            abi.encodeWithSelector(DreggVault.NotDepositor.selector, stranger, address(this))
        );
        vault.escrowRefund(id);
    }

    /// TOOTH: a double refund reverts (the second sees a non-Locked status).
    function test_doubleRefundReverts() public {
        bytes32 id = keccak256("dblrefund");
        uint256 deadline = block.timestamp + 1 days;
        _lockETH(id, 1 ether, deadline);
        vm.warp(deadline + 1);
        vault.escrowRefund(id);

        vm.expectRevert(abi.encodeWithSelector(DreggVault.EscrowNotLocked.selector, id));
        vault.escrowRefund(id);
    }

    // ─── RELEASE guards ─────────────────────────────────────────────────────────

    /// TOOTH: a release without a valid proof reverts (mock verifier rejects).
    function test_prooflessReleaseReverts() public {
        bytes32 id = keccak256("proofless");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);
        verifier.setShouldPass(false);

        vm.expectRevert(DreggVault.ProofVerificationFailed.selector);
        vault.escrowRelease(id, RECIPIENT, _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT));
        // Funds untouched, escrow still Locked.
        assertEq(RECIPIENT.balance, 0);
        assertEq(uint256(vault.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Locked));
    }

    /// TOOTH: a release whose clearing root is NOT proven by the settlement
    /// contract reverts — the fill must reference a genuinely settled clearing.
    function test_releaseWithUnprovenClearingRootReverts() public {
        bytes32 id = keccak256("unproven");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        // NOTE: settlement.setProven NOT called — CLEARING_ROOT is unproven.

        vm.expectRevert(
            abi.encodeWithSelector(DreggVault.ClearingRootNotProven.selector, CLEARING_ROOT)
        );
        vault.escrowRelease(id, RECIPIENT, _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT));
        assertEq(uint256(vault.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Locked));
    }

    /// The zero clearing root is never proven (Nomad-law) — a proof over it reverts.
    function test_releaseWithZeroClearingRootReverts() public {
        bytes32 id = keccak256("zeroroot");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        vm.expectRevert(
            abi.encodeWithSelector(DreggVault.ClearingRootNotProven.selector, bytes32(0))
        );
        vault.escrowRelease(id, RECIPIENT, _fillProof(id, address(0), 1 ether, RECIPIENT, bytes32(0)));
    }

    function test_releaseEscrowIdMismatchReverts() public {
        bytes32 id = keccak256("mm-id");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);
        // Proof names a DIFFERENT escrow id.
        bytes memory proof =
            _fillProof(keccak256("other"), address(0), 1 ether, RECIPIENT, CLEARING_ROOT);
        vm.expectRevert(DreggVault.EscrowIdMismatch.selector);
        vault.escrowRelease(id, RECIPIENT, proof);
    }

    function test_releaseRecipientMismatchReverts() public {
        bytes32 id = keccak256("mm-recip");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);
        // Proof binds RECIPIENT; caller tries to redirect to an attacker.
        bytes memory proof = _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT);
        vm.expectRevert(DreggVault.RecipientMismatch.selector);
        vault.escrowRelease(id, address(0xA77AC6), proof);
    }

    function test_releaseAmountMismatchReverts() public {
        bytes32 id = keccak256("mm-amt");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);
        // Proof claims a different amount than the escrow holds.
        bytes memory proof = _fillProof(id, address(0), 2 ether, RECIPIENT, CLEARING_ROOT);
        vm.expectRevert(DreggVault.AmountMismatch.selector);
        vault.escrowRelease(id, RECIPIENT, proof);
    }

    function test_releaseTokenMismatchReverts() public {
        bytes32 id = keccak256("mm-tok");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);
        // Escrow holds ETH (address(0)); proof claims an ERC-20.
        bytes memory proof = _fillProof(id, address(token), 1 ether, RECIPIENT, CLEARING_ROOT);
        vm.expectRevert(DreggVault.TokenMismatch.selector);
        vault.escrowRelease(id, RECIPIENT, proof);
    }

    /// TOOTH: a double release reverts (the second sees a non-Locked status).
    function test_doubleReleaseReverts() public {
        bytes32 id = keccak256("dblrelease");
        _lockETH(id, 1 ether, block.timestamp + 1 days);
        settlement.setProven(CLEARING_ROOT, true);
        bytes memory proof = _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT);
        vault.escrowRelease(id, RECIPIENT, proof);

        vm.expectRevert(abi.encodeWithSelector(DreggVault.EscrowNotLocked.selector, id));
        vault.escrowRelease(id, RECIPIENT, proof);
        assertEq(RECIPIENT.balance, 1 ether); // paid exactly once
    }

    /// A release on an unknown escrow id reverts (status None != Locked).
    function test_releaseUnknownEscrowReverts() public {
        bytes32 id = keccak256("ghost");
        settlement.setProven(CLEARING_ROOT, true);
        vm.expectRevert(abi.encodeWithSelector(DreggVault.EscrowNotLocked.selector, id));
        vault.escrowRelease(id, RECIPIENT, _fillProof(id, address(0), 1 ether, RECIPIENT, CLEARING_ROOT));
    }

    // ─── DISJOINTNESS: escrow pool ⟂ generic note-mirror pool ───────────────────

    /// The generic `withdraw` path draws only on `tokenBalances`; escrowed funds
    /// live in `escrowedBalances` and are physically present but NOT withdrawable
    /// via the generic path — so the two exit surfaces cannot drain each other.
    function test_genericWithdrawCannotDrainEscrow() public {
        // A tiny GENERIC deposit (establishes a known note root + tokenBalances=0.1).
        vault.depositETH{value: 0.1 ether}(keccak256("generic-note"));
        // A large ESCROW lock of the same asset.
        bytes32 id = keccak256("disjoint");
        _lockETH(id, 1 ether, block.timestamp + 1 days);

        // The contract physically holds 1.1 ETH, but the generic pool is only 0.1;
        // the escrowed 1 ETH is in a disjoint bucket.
        assertEq(vault.tokenBalances(address(0)), 0.1 ether);
        assertEq(vault.escrowedBalances(address(0)), 1 ether);
        assertEq(address(vault).balance, 1.1 ether);

        // A generic withdraw for 1 ETH clears the root gate but fails SOLVENCY: it
        // may only draw the generic 0.1 ETH, never the escrowed 1 ETH.
        bytes memory pv = abi.encode(
            true, keccak256("nf"), address(0), uint256(1 ether), RECIPIENT, vault.noteTreeRoot()
        );
        bytes memory sp1Proof = abi.encode(hex"1234", pv);
        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.InsufficientVaultBalance.selector,
                address(0),
                uint256(1 ether),
                uint256(0.1 ether)
            )
        );
        vault.withdraw(address(0), 1 ether, RECIPIENT, sp1Proof);

        // The escrow is still Locked and fully refundable/releasable.
        assertEq(uint256(vault.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Locked));
        assertEq(vault.escrowedBalances(address(0)), 1 ether);
    }

    // Receive ETH refunds (this contract is the depositor).
    receive() external payable {}
}
