// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggVault.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {MockSP1Verifier, MockSettlement} from "./DreggVault.t.sol";

/// # DrEX ring-of-locks — the cross-chain trade, wired END-TO-END
///
/// This replays a REAL DrEX clearing into the on-chain escrow release. The fixture
/// `test/fixtures/drex_routing.json` is emitted by the Rust routing capstone
/// (`intent/src/drex_routing.rs`, regenerate with `DREX_WRITE_FIXTURE=1 cargo test
/// -p dregg-intent drex_routing::tests::generate_fixture`): it runs the actual flow —
///
///   Solana lock attestation → `MirrorState::verify_lock` (mirror mint, conserving)
///   → `solver.rs` ring matcher (Johnson circuits + Shapley–Scarf TTC)
///   → `verified_settle.rs` (each leg through the proved `recKExecAsset` kernel)
///   → the CLEARING ROOT over the verified post-ledger + one escrow-release
///     instruction per ring leg —
///
/// and hands this test the SAME clearing root the real ring produced, plus, per leg,
/// the escrow id / depositor / recipient / amount. So the value the vault releases
/// against is the value the DrEX ring actually cleared, not a hand-picked constant.
///
/// The lifecycle exercised (`DREX-ROUTING.md §3`):
///   1. LOCK    — each party `escrowDeposit`s its leg into the vault (its own chain's lock).
///   2. CLEAR   — the DrEX ring clears off-chain (the fixture); the clearing proof lands
///                (`settlement.setProven(clearingRoot)` — the rung-8 accept-path; proof
///                VERIFICATION is mocked, the labeled `§4(e)` proof-gen residual).
///   3. RELEASE — each vault `escrowRelease`s to the ring-matched recipient, gated on a
///                fill proof naming the leg + the proven clearing root.
///
/// Both polarities where the escrow has teeth: a cleared ring RELEASES to the
/// counterparties; a lock no ring fills REFUNDS on timeout; an over-release /
/// wrong-recipient / unproven-root release REVERTS.
///
/// HONEST SCOPE: one vault instance stands in for the per-chain vaults (each escrow is
/// one party's lock); the SP1 fill proof + Groth16 settlement proof are mocked (proof-gen
/// is the named `§4(e)` residual); full cross-vault atomic release across a permanently
/// down chain is the `§4(a)` RESEARCH rung. What is REAL here: the clearing root + the
/// per-leg escrow objects, derived from an actual verified, conserving ring clearing.
contract DrexRoutingE2ETest is Test {
    DreggVault public vault;
    MockSP1Verifier public verifier;
    MockSettlement public settlement;

    bytes32 constant PROGRAM_VKEY = bytes32(uint256(0xdeadbeef));

    // Parsed fixture (parallel arrays).
    bytes32 clearingRoot;
    bytes32[] escrowIds;
    address[] depositors;
    address[] recipients;
    uint256[] amounts;

    function setUp() public {
        verifier = new MockSP1Verifier();
        settlement = new MockSettlement();
        vault = new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(address(settlement)));

        string memory json = vm.readFile("test/fixtures/drex_routing.json");
        clearingRoot = vm.parseJsonBytes32(json, ".clearing_root");
        escrowIds = vm.parseJsonBytes32Array(json, ".escrow_ids");
        depositors = vm.parseJsonAddressArray(json, ".depositors");
        recipients = vm.parseJsonAddressArray(json, ".recipients");
        amounts = vm.parseJsonUintArray(json, ".amounts");

        // Sanity: the fixture is a real, non-degenerate ring.
        assertGt(escrowIds.length, 1, "a ring has >1 leg");
        assertEq(escrowIds.length, depositors.length);
        assertEq(escrowIds.length, recipients.length);
        assertEq(escrowIds.length, amounts.length);
        assertTrue(clearingRoot != bytes32(0), "clearing root is non-zero");
    }

    /// Build the SP1 fill-proof envelope naming `escrowId` filled: release `amount` of ETH
    /// (address(0)) to `recipient` under `clearingRoot` — the exact shape `escrowRelease` decodes.
    function _fillProof(bytes32 escrowId, uint256 amount, address recipient, bytes32 root)
        internal
        pure
        returns (bytes memory)
    {
        bytes memory pv = abi.encode(true, escrowId, address(0), amount, recipient, root);
        return abi.encode(hex"1234", pv);
    }

    /// Lock every ring leg into the vault (each party escrows its own leg on its own chain).
    function _lockAllLegs() internal {
        for (uint256 i = 0; i < escrowIds.length; i++) {
            vm.deal(depositors[i], amounts[i]);
            vm.prank(depositors[i]);
            vault.escrowDepositETH{value: amounts[i]}(block.timestamp + 1 days, escrowIds[i]);
            assertEq(uint256(vault.escrowStatus(escrowIds[i])), uint256(DreggVault.EscrowStatus.Locked));
        }
    }

    // ─── THE CAPSTONE: lock → clear → proof → release, end to end ────────────────────

    /// A valid ring RELEASES every leg to its ring-matched recipient, gated on the REAL
    /// clearing root; the vault's escrowed value is fully re-assigned (conserved).
    function test_ringOfLocks_clearsAndReleasesEndToEnd() public {
        // 1. LOCK — every party locks its leg.
        _lockAllLegs();

        uint256 totalLocked = 0;
        for (uint256 i = 0; i < amounts.length; i++) {
            totalLocked += amounts[i];
        }
        assertEq(vault.escrowedBalances(address(0)), totalLocked, "all legs locked, disjoint escrow pool");
        assertEq(address(vault).balance, totalLocked);

        // 2. CLEAR — the DrEX clearing proof lands: dregg proved this clearing root (rung-8
        //    accept-path). Proof VERIFICATION is mocked (the labeled §4(e) proof-gen residual);
        //    the ROOT is the one the real ring produced.
        settlement.setProven(clearingRoot, true);

        // 3. RELEASE — each vault releases to the ring-matched recipient against a fill proof.
        for (uint256 i = 0; i < escrowIds.length; i++) {
            uint256 balBefore = recipients[i].balance;
            bytes memory proof = _fillProof(escrowIds[i], amounts[i], recipients[i], clearingRoot);
            vault.escrowRelease(escrowIds[i], recipients[i], proof);

            // The ring-matched recipient got exactly its leg's value.
            assertEq(recipients[i].balance, balBefore + amounts[i], "recipient paid the leg amount");
            assertEq(
                uint256(vault.escrowStatus(escrowIds[i])),
                uint256(DreggVault.EscrowStatus.Released),
                "leg terminal: Released"
            );
        }

        // Conservation: every escrowed wei was re-assigned to a counterparty; the vault holds none.
        assertEq(vault.escrowedBalances(address(0)), 0, "escrow pool fully re-assigned (conserved)");
        assertEq(address(vault).balance, 0, "no value minted or stranded");
    }

    /// TOOTH (§4(a) refund branch): a lock NO ring fills is reclaimable by its depositor once its
    /// deadline passes — locking into DrEX is safe even when the trade never clears.
    function test_nonClearingLock_refundsOnTimeout() public {
        bytes32 id = keccak256("no-fill-lock");
        address who = address(0xD0);
        uint256 amount = 5 ether;
        uint256 deadline = block.timestamp + 1 days;

        vm.deal(who, amount);
        vm.prank(who);
        vault.escrowDepositETH{value: amount}(deadline, id);

        // No clearing proof ever names this lock. After the deadline, the depositor reclaims.
        vm.warp(deadline + 1);
        vm.prank(who);
        vault.escrowRefund(id);

        assertEq(who.balance, amount, "depositor made whole");
        assertEq(uint256(vault.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Refunded));
        assertEq(vault.escrowedBalances(address(0)), 0);
    }

    /// TOOTH: a release redirected to the WRONG recipient reverts — the fill proof binds the
    /// ring-matched recipient, and the caller cannot substitute an attacker.
    function test_wrongRecipient_reverts() public {
        _lockAllLegs();
        settlement.setProven(clearingRoot, true);

        // The proof binds recipients[0]; caller tries to redirect the payout to an attacker.
        bytes memory proof = _fillProof(escrowIds[0], amounts[0], recipients[0], clearingRoot);
        vm.expectRevert(DreggVault.RecipientMismatch.selector);
        vault.escrowRelease(escrowIds[0], address(0xA77ACC), proof);
    }

    /// TOOTH: an OVER-release (an amount exceeding what the leg locked) reverts — the fill proof's
    /// amount must equal the escrow's exact amount.
    function test_overRelease_reverts() public {
        _lockAllLegs();
        settlement.setProven(clearingRoot, true);

        bytes memory proof = _fillProof(escrowIds[0], amounts[0] + 1 ether, recipients[0], clearingRoot);
        vm.expectRevert(DreggVault.AmountMismatch.selector);
        vault.escrowRelease(escrowIds[0], recipients[0], proof);
    }

    /// TOOTH: a release whose clearing root the settlement contract has NOT proven reverts — the
    /// fill must reference a genuinely settled clearing (here: the proof never landed).
    function test_unprovenClearingRoot_reverts() public {
        _lockAllLegs();
        // settlement.setProven NOT called — the clearing proof never landed.

        bytes memory proof = _fillProof(escrowIds[0], amounts[0], recipients[0], clearingRoot);
        vm.expectRevert(abi.encodeWithSelector(DreggVault.ClearingRootNotProven.selector, clearingRoot));
        vault.escrowRelease(escrowIds[0], recipients[0], proof);
    }

    /// TOOTH: once a leg is Released it is terminal — a second release (double-spend of the lock)
    /// reverts.
    function test_doubleRelease_reverts() public {
        _lockAllLegs();
        settlement.setProven(clearingRoot, true);

        bytes memory proof = _fillProof(escrowIds[0], amounts[0], recipients[0], clearingRoot);
        vault.escrowRelease(escrowIds[0], recipients[0], proof);

        vm.expectRevert(abi.encodeWithSelector(DreggVault.EscrowNotLocked.selector, escrowIds[0]));
        vault.escrowRelease(escrowIds[0], recipients[0], proof);
    }
}
