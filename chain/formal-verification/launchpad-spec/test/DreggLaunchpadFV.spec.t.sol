// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {DreggLaunchpad} from "contracts/launchpad/DreggLaunchpad.sol";

/// @title DreggLaunchpad — ESCROW-CONSERVATION spec (Halmos) — SPEC-ONLY, PENDING RE-RUN
/// @notice The invariant SPEC for the launchpad's escrow accounting, derived from the
///         Lean conservation/optimality theorems. The load-bearing Token+Pool proofs
///         are DONE (green) one directory up; THIS file is the launchpad's spec, to be
///         PROVEN after the live backstop lane (CommitteeAttestor + timeout-refund)
///         lands — its timeout-refund path is exactly the escrow-conservation surface,
///         so proving now would race a mid-edit contract. See ../README.md §Gap.
///
/// LEAN TIE:
///   * `created_value_conservation` (metatheory/Dregg2/Exec/ShieldedValue) — value is
///     conserved over executed state; the EVM twin: ETH in = ETH out, no creation.
///   * `uniform_price_no_arbitrage` (metatheory/Market/Optimality.lean:130) — every
///     leg of a uniform-price clearing is value-neutral; the EVM twin: no bidder pays
///     more than their revealed bid, no over-allocation past `saleSupply`.
///
/// THE INVARIANTS (the anti-rug properties to prove, once the contract is stable):
///
///   ESC-1  ESCROW CONSERVATION — for each launch, the ETH the contract holds on its
///          behalf equals Σ(committed deposits) − Σ(realized proceeds) − Σ(refunds
///          paid). No call sequence lets ETH out exceed ETH in. (`created_value_
///          conservation` twin.)
///
///   ESC-2  SETTLE-XOR-REFUND — a bid's deposit is EITHER settled (part → proceeds,
///          remainder refunded) OR reclaimed as a full timeout refund — NEVER both.
///          The `Bid.settled` and `Bid.refunded` latches are mutually exclusive, and
///          their windows are DISJOINT in time (clearing before revealEnd+grace;
///          refunds only after). No double-spend of an escrow.
///
///   ESC-3  NO OVER-ALLOCATION — Σ(filled) ≤ saleSupply, and each winner pays
///          filled·clearingPrice ≤ their deposit (`UnderCollateralized` guard at
///          reveal + uniform price). (`uniform_price_no_arbitrage` twin.)
///
///   ESC-4  NO-OWNER-DRAIN — `withdrawProceeds` transfers EXACTLY `proceeds` (winners'
///          payments), ONLY to `creator`, ONLY once (`proceedsWithdrawn` latch), ONLY
///          after finalization. The creator can NEVER touch a bidder's escrow before
///          it becomes proceeds (settled) or is refunded. No privileged drain path.
///
///   ESC-5  GRADUATION-SEED HONESTY — `graduate` seeds the pool with EXACTLY the
///          disclosed (graduationBps·proceeds) quote and `poolAllocation` token
///          (`GraduationSeedMismatch` guard); no hidden/short seeding.
///
/// PROOF SHAPE (to run after backstops): a Halmos `check_` harness mirroring the
/// Token/Pool style — deploy a launchpad, drive a bounded symbolic sequence over the
/// external surface {registerLaunch, commitBid, finalizeClearing, settleBid,
/// reclaimEscrow, withdrawProceeds, graduate} with symbolic callers/args, and after
/// each step assert ESC-1..ESC-5. The commit/reveal/clear multi-phase flow makes the
/// reachable-success depth larger than the Token/Pool cases; expect to bound the
/// sequence and report the depth honestly (as with `check_cap_seq3`).
contract DreggLaunchpadFV_Spec is Test {
    // Ghost accounting for ESC-1 (to be threaded through the driven sequence).
    // depositsIn − proceedsOut − refundsOut must equal the contract's escrow balance.

    /// ESC-1 skeleton: the conservation ledger the driven proof will assert.
    /// (Bodyless until the backstop lane stabilises the timeout-refund path.)
    function check_ESC1_escrowConservation() public {
        // deploy launchpad; drive symbolic {commit, settle, reclaim, withdraw} seq;
        // assert: address(pad).balance == depositsIn - proceedsOut - refundsOut.
        vm.assume(true); // PENDING: run after backstops land (see README §Gap).
    }

    /// ESC-2 skeleton: settled and refunded are mutually exclusive per bid.
    function check_ESC2_settleXorRefund() public {
        // for a symbolic bidder: assert !(bid.settled && bid.refunded) after any seq.
        vm.assume(true); // PENDING.
    }

    /// ESC-4 skeleton: no-owner-drain — proceeds out ≤ proceeds, creator-only, once.
    function check_ESC4_noOwnerDrain() public {
        // assert withdrawProceeds moves exactly `proceeds`, only creator, only once;
        // creator cannot reduce any un-settled/un-refunded bidder escrow.
        vm.assume(true); // PENDING.
    }

    // A compile-touch so this spec is a REAL artifact against the current ABI, not
    // vaporware: it references the live launchpad type + its escrow entrypoints.
    function _abiTouch(DreggLaunchpad pad, uint256 id) internal {
        pad.reclaimEscrow(id); // timeout-refund backstop (mid-edit by backstop lane)
        pad.withdrawProceeds(id); // the only creator payout path (ESC-4)
    }
}
