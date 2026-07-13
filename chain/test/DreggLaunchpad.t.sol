// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "../contracts/launchpad/DreggSolventPool.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";

// ─── Mocks (the same MockSettlement pattern as DreggStateOracle.t.sol) ──────────

/// A mock eligibility gate: allowlist by address. Proves the gate WIRING is real
/// (both polarities). A concrete Robinhood-holdings gate wraps the inbound
/// light-client verdict (see ILaunchEligibility docs).
contract MockGate is ILaunchEligibility {
    mapping(address => bool) public ok;

    function allow(address a, bool v) external {
        ok[a] = v;
    }

    function eligible(uint256, address bidder, bytes calldata) external view returns (bool) {
        return ok[bidder];
    }
}

/// A mock clearing attestor: the WIRING for rung-2 (a real dregg Groth16 clearing
/// proof). `accept` toggles the verdict; a real attestor verifies a dregg proof
/// through a pinned Groth16 verifier (the DreggSettlement pattern).
contract MockAttestor is IClearingAttestor {
    bool public accept = true;

    function setAccept(bool v) external {
        accept = v;
    }

    function attestClearing(uint256, uint256, uint256, bytes32, bytes calldata)
        external
        view
        returns (bool)
    {
        return accept;
    }
}

contract DreggLaunchpadTest is Test {
    DreggLaunchpad pad;

    address creator = makeAddr("creator");
    address alice = makeAddr("alice");
    address bob = makeAddr("bob");
    address carol = makeAddr("carol");
    address dave = makeAddr("dave");

    uint64 constant COMMIT_DUR = 100;
    uint64 constant REVEAL_DUR = 100;

    // gwei price units keep the ETH math small but real.
    uint256 constant G = 1e9;

    function setUp() public {
        pad = new DreggLaunchpad();
        vm.deal(creator, 1 ether);
        vm.deal(alice, 1 ether);
        vm.deal(bob, 1 ether);
        vm.deal(carol, 1 ether);
        vm.deal(dave, 1 ether);
    }

    function _schedule() internal pure returns (DreggLaunchpad.Schedule memory s) {
        s = DreggLaunchpad.Schedule({
            totalSupply: 1200,
            saleSupply: 1000,
            creatorAllocation: 100,
            poolAllocation: 100, // reserved to seed the graduated pool
            graduationBps: 5000, // 50% of raise proceeds seed the pool quote reserve
            creatorLockUntil: 0, // set per-test
            reservePrice: 1 * G
        });
    }

    function _register(DreggLaunchpad.Schedule memory s, ILaunchEligibility gate, IClearingAttestor att)
        internal
        returns (uint256 id)
    {
        vm.prank(creator);
        id = pad.registerLaunch("DreggMeme", "DMEME", s, COMMIT_DUR, REVEAL_DUR, gate, att);
    }

    function _commit(uint256 id, address who, uint256 price, uint256 qty, bytes32 salt) internal {
        bytes32 seal = pad.sealOf(price, qty, salt, who);
        vm.prank(who);
        pad.commitBid{value: price * qty}(id, seal, "");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // POLARITY 1 — A GENUINE FAIR LAUNCH RUNS (commit → reveal → uniform clear →
    // settle), and every winner pays the SAME uniform price.
    // ══════════════════════════════════════════════════════════════════════════

    function test_FairLaunchRunsAndClearsUniform() public {
        DreggLaunchpad.Schedule memory s = _schedule();
        uint256 id = _register(s, ILaunchEligibility(address(0)), IClearingAttestor(address(0)));

        // Disclosure is publicly checkable; a tampered schedule does NOT match.
        assertTrue(pad.checkSchedule(id, s), "disclosed schedule must match commit");
        DreggLaunchpad.Schedule memory tampered = s;
        tampered.totalSupply = 999999;
        assertFalse(pad.checkSchedule(id, tampered), "a hidden-supply schedule must NOT match");

        // (b) sealed commits — bids 5,4,3,2 gwei/token, qty 400 each.
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 4 * G, 400, keccak256("b"));
        _commit(id, carol, 3 * G, 400, keccak256("c"));
        _commit(id, dave, 2 * G, 400, keccak256("d"));

        // Reveal window — reveal in SCRAMBLED order (dave, alice, carol, bob).
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(dave);
        pad.revealBid(id, 2 * G, 400, keccak256("d")); // index 0
        vm.prank(alice);
        pad.revealBid(id, 5 * G, 400, keccak256("a")); // index 1
        vm.prank(carol);
        pad.revealBid(id, 3 * G, 400, keccak256("c")); // index 2
        vm.prank(bob);
        pad.revealBid(id, 4 * G, 400, keccak256("b")); // index 3

        // (c) uniform-price clearing. Sorted desc by price: alice(1) bob(3)
        // carol(2) dave(0). saleSupply=1000 → alice 400, bob 400, carol 200
        // (marginal), dave 0. Uniform clearing price = carol's 3 gwei.
        vm.warp(block.timestamp + REVEAL_DUR);
        uint256[] memory order = new uint256[](4);
        order[0] = 1; // alice
        order[1] = 3; // bob
        order[2] = 2; // carol
        order[3] = 0; // dave
        pad.finalizeClearing(id, order, "");

        assertEq(pad.clearingPriceOf(id), 3 * G, "uniform clearing price = marginal (carol)");
        assertEq(pad.soldQtyOf(id), 1000, "full saleSupply cleared");

        // (d) settle — EVERY winner pays the SAME uniform price (3 gwei), gets
        // tokens, is refunded the rest of the deposit.
        DreggLaunchToken tok = DreggLaunchToken(pad.tokenOf(id));

        _settleAndAssert(pad, id, alice, 400, 3 * G, 5 * G, 400, tok);
        _settleAndAssert(pad, id, bob, 400, 3 * G, 4 * G, 400, tok);
        _settleAndAssert(pad, id, carol, 200, 3 * G, 3 * G, 400, tok); // partial fill
        _settleAndAssert(pad, id, dave, 0, 3 * G, 2 * G, 400, tok); // no fill, full refund

        // Proceeds = uniform_price * total_sold = 3 gwei * 1000.
        uint256 expectedProceeds = 3 * G * 1000;
        uint256 balBefore = creator.balance;
        vm.prank(creator);
        pad.withdrawProceeds(id);
        assertEq(creator.balance - balBefore, expectedProceeds, "creator gets the raise proceeds");
    }

    /// Settle `who`, assert fill/refund/token award and the uniform payment.
    function _settleAndAssert(
        DreggLaunchpad pad_,
        uint256 id,
        address who,
        uint256 expFill,
        uint256 clearing,
        uint256 bidPrice,
        uint256 bidQty,
        DreggLaunchToken tok
    ) internal {
        uint256 ethBefore = who.balance;
        pad_.settleBid(id, who);
        uint256 payment = clearing * expFill;
        uint256 deposit = bidPrice * bidQty;
        uint256 refund = deposit - payment;
        assertEq(who.balance - ethBefore, refund, "refund = deposit - uniform payment");
        assertEq(tok.balanceOf(who), expFill * pad_.TOKEN_UNIT(), "token award = filled qty");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // POLARITY 2 — ABUSE ATTEMPTS REVERT
    // ══════════════════════════════════════════════════════════════════════════

    // ── (i) NO HIDDEN SUPPLY ────────────────────────────────────────────────────

    /// A schedule whose parts do not account for the cap (hidden supply) reverts.
    function test_HiddenSupplyScheduleReverts() public {
        DreggLaunchpad.Schedule memory s = _schedule();
        s.saleSupply = 1000;
        s.creatorAllocation = 200;
        s.totalSupply = 5000; // 3800 tokens hidden — does not close
        vm.prank(creator);
        vm.expectRevert(
            abi.encodeWithSelector(DreggLaunchpad.SupplyDoesNotClose.selector, uint256(1000), uint256(200), uint256(5000))
        );
        pad.registerLaunch("X", "X", s, COMMIT_DUR, REVEAL_DUR, ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
    }

    /// The token has NO second mint door — a hidden post-launch inflation reverts.
    function test_TokenHasNoSecondMintDoor() public {
        // Deploy a token with this test as the minter (mirrors the launchpad's role).
        DreggLaunchToken tok = new DreggLaunchToken("T", "T", 1000, address(this));
        tok.mint(address(this), 1000); // the single disclosed mint
        assertEq(tok.totalSupply(), 1000);

        vm.expectRevert(DreggLaunchToken.AlreadyMinted.selector);
        tok.mint(address(this), 1); // hidden supply — no second door

        // Over-cap and non-minter also fail closed.
        DreggLaunchToken tok2 = new DreggLaunchToken("T2", "T2", 1000, address(this));
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchToken.CapExceeded.selector, uint256(1001), uint256(1000)));
        tok2.mint(address(this), 1001);

        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchToken.NotMinter.selector, alice));
        tok2.mint(alice, 1);
    }

    // ── (ii) NO SNIPE / NO PEEK ─────────────────────────────────────────────────

    /// Revealing during the commit window (peeking before the seal) reverts — no
    /// bid is observable before clearing.
    function test_PeekBeforeRevealPhaseReverts() public {
        uint256 id = _register(_schedule(), ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        // Still in commit window — reveal must fail closed.
        vm.prank(alice);
        vm.expectRevert(DreggLaunchpad.NotRevealPhase.selector);
        pad.revealBid(id, 5 * G, 400, keccak256("a"));
    }

    /// A reveal that does not OPEN the committed seal (a late-switch to a
    /// different bid after seeing others) reverts.
    function test_LateSwitchRevealReverts() public {
        uint256 id = _register(_schedule(), ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        vm.warp(block.timestamp + COMMIT_DUR);
        // Reveal a DIFFERENT bid (price 9) than the committed one — cannot open.
        vm.prank(alice);
        vm.expectRevert(DreggLaunchpad.BidMismatch.selector);
        pad.revealBid(id, 9 * G, 400, keccak256("a"));
    }

    /// A fresh launch-block wallet that never committed cannot reveal/win.
    function test_UncommittedCannotReveal() public {
        uint256 id = _register(_schedule(), ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(bob); // bob never committed
        vm.expectRevert(DreggLaunchpad.NoCommit.selector);
        pad.revealBid(id, 5 * G, 400, keccak256("x"));
    }

    // ── (iii) NON-UNIFORM CLEARING REJECTED ─────────────────────────────────────

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

    /// A clearing order that is NOT sorted descending (an attempt to clear in a
    /// non-canonical / non-uniform way) reverts.
    function test_NonUniformOrderRejected() public {
        uint256 id = _register(_schedule(), ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
        _setupTwoRevealed(id);
        // order [1,0] presents bob(3) before alice(5): 3 <= 5 ok going down, but
        // this claims ascending — walk sees 3 then 5 (5 > prev 3) → reject.
        uint256[] memory order = new uint256[](2);
        order[0] = 1; // bob (3)
        order[1] = 0; // alice (5)
        vm.expectRevert(DreggLaunchpad.NotSortedDescending.selector);
        pad.finalizeClearing(id, order, "");
    }

    /// A clearing order that is not a PERMUTATION (drops/inserts a bid) reverts —
    /// no hidden allocation can be inserted into the cleared book.
    function test_BadPermutationRejected() public {
        uint256 id = _register(_schedule(), ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
        _setupTwoRevealed(id);
        uint256[] memory dup = new uint256[](2);
        dup[0] = 0;
        dup[1] = 0; // alice twice — bob dropped
        vm.expectRevert(DreggLaunchpad.BadPermutation.selector);
        pad.finalizeClearing(id, dup, "");

        uint256[] memory oob = new uint256[](2);
        oob[0] = 0;
        oob[1] = 5; // out of range — inserts a non-bid
        vm.expectRevert(DreggLaunchpad.BadPermutation.selector);
        pad.finalizeClearing(id, oob, "");
    }

    // ── (iv) DEV-DUMP GUARD (creator vesting lock) ──────────────────────────────

    function test_CreatorAllocationLockedUntilCliff() public {
        DreggLaunchpad.Schedule memory s = _schedule();
        s.creatorLockUntil = uint64(block.timestamp) + 10_000; // a real cliff
        uint256 id = _register(s, ILaunchEligibility(address(0)), IClearingAttestor(address(0)));

        // Before the cliff: the creator CANNOT pull its allocation.
        vm.prank(creator);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.CreatorLockActive.selector, s.creatorLockUntil));
        pad.claimCreatorAllocation(id);

        // After the cliff: it unlocks (the disclosed schedule, honored).
        vm.warp(s.creatorLockUntil);
        vm.prank(creator);
        pad.claimCreatorAllocation(id);
        DreggLaunchToken tok = DreggLaunchToken(pad.tokenOf(id));
        assertEq(tok.balanceOf(creator), s.creatorAllocation * pad.TOKEN_UNIT(), "creator alloc released at cliff");
    }

    // ── (v) ELIGIBILITY GATE (the Robinhood-holdings composition seam) ──────────

    function test_EligibilityGateEnforced() public {
        MockGate gate = new MockGate();
        uint256 id = _register(_schedule(), gate, IClearingAttestor(address(0)));

        // Ineligible bidder is refused at commit.
        bytes32 seal = pad.sealOf(5 * G, 400, keccak256("a"), alice);
        vm.prank(alice);
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.NotEligible.selector, alice));
        pad.commitBid{value: 5 * G * 400}(id, seal, "");

        // Allowlisted bidder is accepted.
        gate.allow(alice, true);
        vm.prank(alice);
        pad.commitBid{value: 5 * G * 400}(id, seal, "");
        (bool committed,,,,,,) = pad.getBid(id, alice);
        assertTrue(committed, "eligible bidder committed");
    }

    // ── (vi) CLEARING ATTESTOR (rung-2 dregg-proof wiring) ──────────────────────

    function test_ClearingAttestorAcceptAndReject() public {
        MockAttestor att = new MockAttestor();
        uint256 id = _register(_schedule(), ILaunchEligibility(address(0)), att);
        _setupTwoRevealed(id);

        uint256[] memory order = new uint256[](2);
        order[0] = 0; // alice (5)
        order[1] = 1; // bob (3)

        // Reject polarity: a failing attestation blocks the clearing.
        att.setAccept(false);
        vm.expectRevert(DreggLaunchpad.ClearingNotAttested.selector);
        pad.finalizeClearing(id, order, hex"1234");

        // Accept polarity: a passing attestation records the PROVED rung.
        att.setAccept(true);
        pad.finalizeClearing(id, order, hex"1234");
        assertTrue(pad.clearingAttested(id), "clearing attested by dregg proof (rung 2)");
        // Undersubscribed (800 < 1000): both win, uniform price = lowest winner (bob, 3 gwei).
        assertEq(pad.clearingPriceOf(id), 3 * G, "uniform price = lowest winning bid (bob)");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // GRADUATION — the cleared raise graduates into a PROVABLY-SOLVENT liquid
    // market (§2.3). Seed = a DISCLOSED fraction of the raise; trades cannot drain
    // the pool below its floor (rung-6 pool_solvent_forever, on-chain).
    // ══════════════════════════════════════════════════════════════════════════

    /// Run a full fair launch to CLEARED + all winners SETTLED (proceeds realized).
    /// alice 5, bob 4, carol 3, dave 2 gwei × 400 → clear @ 3 gwei, sold 1000,
    /// proceeds = 3 gwei × 1000 = 3000 gwei. Returns the launch id.
    function _runToSettled() internal returns (uint256 id) {
        id = _register(_schedule(), ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 4 * G, 400, keccak256("b"));
        _commit(id, carol, 3 * G, 400, keccak256("c"));
        _commit(id, dave, 2 * G, 400, keccak256("d"));
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(alice);
        pad.revealBid(id, 5 * G, 400, keccak256("a")); // index 0
        vm.prank(bob);
        pad.revealBid(id, 4 * G, 400, keccak256("b")); // index 1
        vm.prank(carol);
        pad.revealBid(id, 3 * G, 400, keccak256("c")); // index 2
        vm.prank(dave);
        pad.revealBid(id, 2 * G, 400, keccak256("d")); // index 3
        vm.warp(block.timestamp + REVEAL_DUR);
        uint256[] memory order = new uint256[](4);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;
        order[3] = 3;
        pad.finalizeClearing(id, order, "");
        pad.settleBid(id, alice);
        pad.settleBid(id, bob);
        pad.settleBid(id, carol);
        pad.settleBid(id, dave);
    }

    /// The canonical disclosed seed for the standard launch: 50% of 3000 gwei
    /// proceeds = 1500 gwei quote; 100 whole tokens.
    uint256 constant EXP_QUOTE_SEED = 1500 * G; // 1500 gwei wei
    uint256 constant EXP_TOKEN_SEED = 100 * 1e18;

    // ── (i) GRADUATION RUNS: seed the solvent pool, trades clear against it ──────

    function test_GraduatesToSolventPoolAndTrades() public {
        uint256 id = _runToSettled();

        // The disclosed seed is on-chain-verifiable (deterministic from cleared state).
        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);
        assertEq(qSeed, EXP_QUOTE_SEED, "quote seed = graduationBps (50%) of proceeds");
        assertEq(tSeed, EXP_TOKEN_SEED, "token seed = disclosed poolAllocation");

        uint256 padBalBefore = address(pad).balance;
        DreggSolventPool pool = DreggSolventPool(pad.graduate(id, qSeed, tSeed));
        assertTrue(pad.isGraduated(id), "launch graduated");
        assertEq(pad.poolOf(id), address(pool), "pool recorded");
        // The seed ETH left the launchpad and is in the pool.
        assertEq(padBalBefore - address(pad).balance, EXP_QUOTE_SEED, "seed ETH left the launchpad");
        assertEq(address(pool).balance, EXP_QUOTE_SEED, "seed ETH is in the pool");

        _assertSeededPool(pool);
        _assertBuyClears(pool);

        // The creator withdraws only the REMAINDER (proceeds - seed).
        uint256 balBefore = creator.balance;
        vm.prank(creator);
        pad.withdrawProceeds(id);
        assertEq(creator.balance - balBefore, 3 * G * 1000 - EXP_QUOTE_SEED, "creator gets proceeds minus seed");
    }

    /// The graduated pool is seeded with exactly the disclosed reserves + floors.
    function _assertSeededPool(DreggSolventPool pool) internal view {
        (uint256 rq, uint256 rt) = pool.reserves();
        assertEq(rq, EXP_QUOTE_SEED, "pool quote reserve = seed");
        assertEq(rt, EXP_TOKEN_SEED, "pool token reserve = seed");
        // Floors = 20% of the seed (the disclosed reserve floor, rung-6).
        (uint256 fq, uint256 ft) = pool.floors();
        assertEq(fq, EXP_QUOTE_SEED * 2000 / 10000, "quote floor = 20% of seed");
        assertEq(ft, EXP_TOKEN_SEED * 2000 / 10000, "token floor = 20% of seed");
        // Spot price = reserveQuote·1e18 / reserveToken.
        assertEq(pool.spotPriceWeiPerToken(), (EXP_QUOTE_SEED * 1e18) / EXP_TOKEN_SEED, "honest spot price");
    }

    /// A live buy clears against the never-insolvent pool; reserves move, x*y grows,
    /// the floor holds.
    function _assertBuyClears(DreggSolventPool pool) internal {
        (uint256 rq, uint256 rt) = pool.reserves();
        (, uint256 ft) = pool.floors();
        uint256 kBefore = rq * rt;
        vm.deal(alice, 1 ether);
        uint256 tokBefore = pool.token().balanceOf(alice);
        vm.prank(alice);
        uint256 out = pool.buy{value: 100 * G}(0);
        assertGt(out, 0, "buy delivered tokens");
        assertEq(pool.token().balanceOf(alice) - tokBefore, out, "buyer received the tokens");
        (uint256 rq2, uint256 rt2) = pool.reserves();
        assertEq(rq2, rq + 100 * G, "quote reserve grew by the input");
        assertEq(rt2, rt - out, "token reserve fell by the output");
        assertGe(rq2 * rt2, kBefore, "x*y non-decreasing (constant product)");
        assertGe(rt2, ft, "token reserve stayed above the floor");
    }

    // ── (ii) THE SOLVENCY TOOTH: a drain below the floor REVERTS ─────────────────

    function test_SolvencyDrainReverts() public {
        uint256 id = _runToSettled();
        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);
        DreggSolventPool pool = DreggSolventPool(pad.graduate(id, qSeed, tSeed));

        // A whale buy whose output would push the token reserve below the floor
        // (20% = 20 tokens) REVERTS — the pool cannot be drained (rung-6).
        vm.deal(bob, 100 ether);
        vm.prank(bob);
        // The floor bites: PoolFloorBreached(reserveAfter, floorToken) — match the
        // selector, ignore the (computed) args.
        vm.expectPartialRevert(DreggSolventPool.PoolFloorBreached.selector);
        pool.buy{value: 20_000 * G}(0);

        // Sanity: reserves untouched by the reverted trade.
        (uint256 rq, uint256 rt) = pool.reserves();
        assertEq(rq, EXP_QUOTE_SEED, "quote reserve unchanged after revert");
        assertEq(rt, EXP_TOKEN_SEED, "token reserve unchanged after revert");

        // A modest buy within the floor still clears (both polarities).
        vm.deal(bob, 1 ether);
        vm.prank(bob);
        uint256 out = pool.buy{value: 50 * G}(0);
        assertGt(out, 0, "a within-floor buy clears");
    }

    // ── (iii) DISCLOSED FRACTION ENFORCED: a wrong/hidden seeding REVERTS ────────

    function test_GraduationSeedMismatchReverts() public {
        uint256 id = _runToSettled();
        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);

        // Under-seeding the pool (skimming quote) reverts.
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.GraduationSeedMismatch.selector, qSeed, tSeed));
        pad.graduate(id, qSeed - 1, tSeed);

        // Wrong token seed reverts.
        vm.expectRevert(abi.encodeWithSelector(DreggLaunchpad.GraduationSeedMismatch.selector, qSeed, tSeed));
        pad.graduate(id, qSeed, tSeed + 1);

        // The correct disclosed seed graduates.
        pad.graduate(id, qSeed, tSeed);
        assertTrue(pad.isGraduated(id), "correct seed graduates");
    }

    // ── (iv) SETTLE-FIRST GATE + no double graduation ───────────────────────────

    function test_GraduationRequiresSettlement() public {
        // Run to CLEARED but leave a winner unsettled → realized proceeds short.
        uint256 id = _register(_schedule(), ILaunchEligibility(address(0)), IClearingAttestor(address(0)));
        _commit(id, alice, 5 * G, 400, keccak256("a"));
        _commit(id, bob, 4 * G, 400, keccak256("b"));
        _commit(id, carol, 3 * G, 400, keccak256("c"));
        _commit(id, dave, 2 * G, 400, keccak256("d"));
        vm.warp(block.timestamp + COMMIT_DUR);
        vm.prank(alice);
        pad.revealBid(id, 5 * G, 400, keccak256("a"));
        vm.prank(bob);
        pad.revealBid(id, 4 * G, 400, keccak256("b"));
        vm.prank(carol);
        pad.revealBid(id, 3 * G, 400, keccak256("c"));
        vm.prank(dave);
        pad.revealBid(id, 2 * G, 400, keccak256("d"));
        vm.warp(block.timestamp + REVEAL_DUR);
        uint256[] memory order = new uint256[](4);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;
        order[3] = 3;
        pad.finalizeClearing(id, order, "");
        pad.settleBid(id, alice); // only alice settled → proceeds < canonical

        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);
        vm.expectRevert(); // GraduationRequiresSettlement(realized, canonical)
        pad.graduate(id, qSeed, tSeed);

        // Settle the rest → graduation proceeds.
        pad.settleBid(id, bob);
        pad.settleBid(id, carol);
        pad.settleBid(id, dave);
        pad.graduate(id, qSeed, tSeed);
        assertTrue(pad.isGraduated(id), "graduates once fully settled");

        // Cannot graduate twice.
        vm.expectRevert(DreggLaunchpad.AlreadyGraduated.selector);
        pad.graduate(id, qSeed, tSeed);
    }

    function test_CannotGraduateAfterProceedsWithdrawn() public {
        uint256 id = _runToSettled();
        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);
        vm.prank(creator);
        pad.withdrawProceeds(id); // creator took the ETH first
        vm.expectRevert(DreggLaunchpad.ProceedsAlreadyWithdrawn.selector);
        pad.graduate(id, qSeed, tSeed);
    }
}
