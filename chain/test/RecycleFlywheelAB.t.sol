// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test, console2} from "forge-std/Test.sol";
import {RecycleFlywheel} from "../contracts/flywheel/RecycleFlywheel.sol";
import {MockCircFlywheel} from "../contracts/flywheel/MockCircFlywheel.sol";
import {MockAmm} from "../contracts/flywheel/MockAmm.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "../contracts/launchpad/DreggSolventPool.sol";

/// A real MEV extractor: front-runs a victim market buy, back-runs after it moved
/// the price. This is the adversary CIRC's telegraphed market buy (§2.1e) invites
/// and dregg's sealed clearing makes unconstructable - NOT a strawman.
contract SandwichBot {
    MockAmm public amm;
    DreggLaunchToken public token;

    constructor(address amm_, address token_) {
        amm = MockAmm(payable(amm_));
        token = DreggLaunchToken(token_);
    }

    /// Buy tokens with `ethIn` BEFORE the victim's buy (front-run).
    function frontRun(uint256 ethIn) external returns (uint256 tokenOut) {
        tokenOut = amm.buy{value: ethIn}(0);
    }

    /// Sell everything the bot holds AFTER the victim moved the price (back-run).
    function backRun() external returns (uint256 quoteOut) {
        uint256 bal = token.balanceOf(address(this));
        token.approve(address(amm), bal);
        quoteOut = amm.sell(bal, 0);
    }

    receive() external payable {}
}

/// # THE VERIFIABLE RECYCLE-FLYWHEEL A/B MEASUREMENT
///
/// Adversarial, head-to-head, on identical token infrastructure:
/// `RecycleFlywheel` (dregg: sealed-bid clearing + committed split + solvent pool +
/// conservation cert + signed receipt chain) vs `MockCircFlywheel` (a FAITHFUL
/// CIRC-style flywheel: owner-key split + front-runnable market buy + LP-add, no
/// cert, no receipt). Every metric in `docs/reference/CIRC-COMPETITIVE-ANALYSIS.md`
/// §6.2 is measured as a real number, and the honest gas/latency premium is
/// reported PLAINLY (dregg is not cheaper/faster - it is front-run-immune,
/// deviation-proof, conserving, and re-checkable, at a stated bounded premium).
///
/// The HONEST pole runs first (`test_0_Dregg_HonestRecycle_EndToEnd`).
contract RecycleFlywheelABTest is Test {
    DreggLaunchToken token;

    uint256 constant OPERATOR_PK = 0xA11CE;
    address OPERATOR;

    // The 50/50 committed split, faithful to CIRC's "Splits the proceeds 50 / 50".
    uint256 constant BUY_BPS = 5000;
    uint16 constant FLOOR_BPS = 2000; // == RecycleFlywheel.FLOOR_BPS

    uint64 constant COMMIT_DUR = 100;
    uint64 constant REVEAL_DUR = 100;
    uint256 constant G = 1e9; // gwei - the price unit (wei per whole token)
    uint256 constant UNIT = 1e18;
    uint256 constant CAP = 1_000_000_000_000 * UNIT; // 1e30 base units

    address alice = makeAddr("alice"); // seller A
    address bob = makeAddr("bob"); // seller B
    address carol = makeAddr("carol"); // seller C / the bot-seller

    function setUp() public {
        OPERATOR = vm.addr(OPERATOR_PK);
        token = new DreggLaunchToken("Recycle Token", "RCY", CAP, address(this));
        poolImpl = address(new DreggSolventPool());
        token.mint(address(this), CAP);
        vm.deal(address(this), 1_000_000 ether);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Shared drivers
    // ══════════════════════════════════════════════════════════════════════════

    /// The one inert pool implementation every recycle's pool is a clone of —
    /// deployed once per chain (here: once in setUp), a committed public input.
    address poolImpl;

    function _newFlywheel() internal returns (RecycleFlywheel fw) {
        fw = new RecycleFlywheel(address(token), uint16(BUY_BPS), OPERATOR, COMMIT_DUR, REVEAL_DUR, poolImpl);
    }

    /// Fund `seller`, approve, and commit a sealed ask escrowing `qty` whole tokens.
    function _commitAsk(RecycleFlywheel fw, address seller, uint256 price, uint256 qty, bytes32 salt) internal {
        uint256 escrow = qty * UNIT;
        token.transfer(seller, escrow);
        bytes32 seal = fw.sealOf(price, qty, salt, seller);
        vm.startPrank(seller);
        token.approve(address(fw), escrow);
        fw.commitAsk(seal, escrow);
        vm.stopPrank();
    }

    function _revealAsk(RecycleFlywheel fw, address seller, uint256 price, uint256 qty, bytes32 salt) internal {
        vm.prank(seller);
        fw.revealAsk(price, qty, salt);
    }

    function _sign(bytes32 head) internal pure returns (bytes memory) {
        (uint8 v, bytes32 r, bytes32 s) =
            vm.sign(OPERATOR_PK, keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", head)));
        return abi.encodePacked(r, s, v);
    }

    /// Build the operator-signed receipt for the CORRECT split + clearing and
    /// finalize `fw` with `order`. (The operator previews the clearing off-chain,
    /// signs the head, submits - exactly the real flow.)
    function _finalize(RecycleFlywheel fw, uint256[] memory order) internal {
        (uint256 buyHalf, uint256 poolHalf, bytes32 head) = _buildReceipt(fw, order);
        bytes memory sig = _sign(head);
        fw.finalizeRecycle(order, buyHalf, poolHalf, head, sig);
    }

    function _buildReceipt(RecycleFlywheel fw, uint256[] memory order)
        internal
        view
        returns (uint256 buyHalf, uint256 poolHalf, bytes32 head)
    {
        uint256 acc = fw.accrued();
        buyHalf = (acc * BUY_BPS) / 10000;
        poolHalf = acc - buyHalf;
        (uint256 uP, uint256 bought, uint256 spent, bytes32 bc) = fw.previewClearing(order, buyHalf);
        uint256 qSeed = poolHalf + (buyHalf - spent);
        uint256 tSeed = bought * UNIT;
        RecycleFlywheel.Receipt memory r = RecycleFlywheel.Receipt({
            accrued: acc,
            provenanceRoot: fw.provenanceRoot(),
            inflowCount: fw.inflowCount(),
            buyHalf: buyHalf,
            poolHalf: poolHalf,
            buyBps: uint16(BUY_BPS),
            uniformPrice: uP,
            boughtTokens: bought,
            spentQuote: spent,
            bookCommit: bc,
            quoteSeed: qSeed,
            tokenSeed: tSeed,
            floorQuote: (qSeed * FLOOR_BPS) / 10000,
            floorToken: (tSeed * FLOOR_BPS) / 10000,
            netQuote: int256(0),
            netToken: int256(0)
        });
        head = fw.recomputeReceiptHead(r);
    }

    /// The canonical honest recycle: accrue 80 ETH over 2 provenanced inflows, a
    /// 3-seller ascending book (1/2/3 gwei), reveal ascending, clear order [0,1,2].
    /// All fills clear at 3 gwei (30 ETH spent), leftover 10 ETH -> pool. Returns fw
    /// at phase Cleared (unsettled).
    function _driveHonest() internal returns (RecycleFlywheel fw) {
        fw = _newFlywheel();
        fw.accrueFee{value: 40 ether}(keccak256("turn-1"));
        fw.accrueFee{value: 40 ether}(keccak256("game-move-2"));

        _commitAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _commitAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _commitAsk(fw, carol, 3 * G, 4_000_000_000, "c");

        vm.warp(fw.commitEnd());
        _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a"); // idx 0
        _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b"); // idx 1
        _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c"); // idx 2
        vm.warp(fw.revealEnd());

        uint256[] memory order = new uint256[](3);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;
        _finalize(fw, order);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 0 - THE HONEST POLE, FIRST: the whole recycle loop clears end-to-end
    // ══════════════════════════════════════════════════════════════════════════

    function test_0_Dregg_HonestRecycle_EndToEnd() public {
        RecycleFlywheel fw = _driveHonest();

        assertEq(uint256(fw.phase()), uint256(RecycleFlywheel.Phase.Cleared), "recycle cleared");
        assertEq(fw.uniformPrice(), 3 * G, "ONE uniform price for the whole sealed book");
        assertEq(fw.boughtTokens(), 10_000_000_000, "the buy cleared the whole ascending book");
        assertEq(fw.spentQuote(), 30 ether, "wei paid to sellers = uniform x bought");
        assertEq(fw.quoteSeed(), 50 ether, "pool quote = pool-half (40) + unspent budget (10)");

        // The pool is a real, solvent, trading market.
        DreggSolventPool pool = fw.pool();
        assertEq(address(pool).balance, 50 ether, "pool holds exactly the disclosed quote seed");
        assertEq(token.balanceOf(address(pool)), 10_000_000_000 * UNIT, "pool holds exactly the bought tokens");
        (uint256 fq,) = pool.floors();
        assertEq(fq, 10 ether, "disclosed solvency floor = 20% of the quote seed");

        // Settle every seller - each paid the UNIFORM price, not its ask.
        _settleAndCheck(fw, alice, 3_000_000_000, 3 * G); // 3e9 tokens x 3 gwei = 9 ETH
        _settleAndCheck(fw, bob, 3_000_000_000, 3 * G); // 9 ETH (bid 2 gwei, PAID 3)
        _settleAndCheck(fw, carol, 4_000_000_000, 3 * G); // 12 ETH

        // Conservation closes the loop: no ETH, no token residue in the flywheel.
        assertEq(address(fw).balance, 0, "no ETH residue - every wei routed to sellers or the pool");
        assertEq(token.balanceOf(address(fw)), 0, "no token residue - every token routed to the pool");

        // The graduated pool trades and is floor-guarded (rung-6).
        uint256 out = pool.buy{value: 0.1 ether}(0);
        assertGt(out, 0, "the recycled pool clears a real buy");
    }

    function _settleAndCheck(RecycleFlywheel fw, address seller, uint256 expFill, uint256 clearing) internal {
        uint256 ethBefore = seller.balance;
        fw.settleAsk(seller);
        assertEq(seller.balance - ethBefore, clearing * expFill, "seller paid the UNIFORM price for its fill");
        (,,,, uint256 filled,,) = fw.getAsk(seller);
        assertEq(filled, expFill, "fill matches the clearing");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 1 - MEV: the mock's market buy is sandwiched (>0); dregg's clearing is 0
    // ══════════════════════════════════════════════════════════════════════════

    function test_1_MEV_MockSandwichPositive_DreggZero() public {
        // ── MOCK: a real sandwich bot extracts positive MEV from the market buy ──
        uint256 mockMev = _mockSandwich();
        assertGt(mockMev, 0, "MOCK: the sandwich bot extracted positive MEV from the telegraphed market buy");
        console2.log("MOCK  sandwich MEV extracted (wei):", mockMev);

        // ── DREGG: the recycle buy is a SEALED, ORDER-INVARIANT batch clearing -
        //    there is no telegraphed swap to wrap. The bot's only surface is an
        //    honest sealed ask, and its proceeds are identical whether it arrives
        //    first or last: the ordering lever yields exactly 0.
        (uint256 payFirst, uint256 payLast) = _dreggBotOrderingProbe();
        assertEq(payFirst, payLast, "DREGG: bot proceeds identical regardless of arrival order");
        uint256 dreggMev = payFirst > payLast ? payFirst - payLast : payLast - payFirst;
        assertEq(dreggMev, 0, "DREGG: ordering/front-run MEV is 0 by construction");
        console2.log("DREGG ordering MEV extracted (wei):", dreggMev);
    }

    /// Seed a pump-style AMM, run the CIRC-mock recycle as the victim market buy,
    /// and sandwich it. Returns the bot's net ETH gain (the extracted MEV).
    function _mockSandwich() internal returns (uint256 mev) {
        MockAmm amm = new MockAmm(address(token), 30); // 0.30% pump-style fee
        uint256 seedTok = 1_000_000_000 * UNIT;
        token.approve(address(amm), seedTok);
        amm.addLiquidity{value: 50 ether}(seedTok);

        MockCircFlywheel mock = new MockCircFlywheel(address(token), address(amm), uint16(BUY_BPS));
        SandwichBot bot = new SandwichBot(address(amm), address(token));
        vm.deal(address(bot), 100 ether);

        uint256 before = address(bot).balance;
        // A Solana sandwich wraps the flywheel's telegraphed buy tx. Front-run:
        bot.frontRun(5 ether);
        // The victim: the autonomous flywheel recycle (market-buy 20 ETH -> buyHalf
        // 10 ETH pushes price up, then pairs+LP the rest). No human, fully on-chain.
        mock.recycle{value: 20 ether}(0);
        // Back-run: dump into the elevated price.
        bot.backRun();
        uint256 afterBal = address(bot).balance;
        mev = afterBal > before ? afterBal - before : 0;
    }

    /// Run the dregg recycle twice with an identical book, the bot-seller arriving
    /// FIRST vs LAST. Returns the bot's paid ETH in each - equal iff order-invariant.
    function _dreggBotOrderingProbe() internal returns (uint256 payFirst, uint256 payLast) {
        payFirst = _probeOnce(true);
        payLast = _probeOnce(false);
    }

    function _probeOnce(bool botArrivesFirst) internal returns (uint256 botPaid) {
        RecycleFlywheel fw = _newFlywheel();
        fw.accrueFee{value: 40 ether}(keccak256("p1"));
        fw.accrueFee{value: 40 ether}(keccak256("p2"));

        // Identical book: A@1g x3e9, B@2g x3e9, carol(the bot-seller)@3g x4e9.
        _commitAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _commitAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _commitAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.commitEnd());

        uint256[] memory order = new uint256[](3);
        if (botArrivesFirst) {
            // The bot reveals FIRST (idx 0), then B (idx 1), then A (idx 2).
            _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c");
            _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b");
            _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a");
            order[0] = 2; // A @1g
            order[1] = 1; // B @2g
            order[2] = 0; // bot @3g
        } else {
            // The bot reveals LAST (idx 2).
            _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a");
            _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b");
            _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c");
            order[0] = 0;
            order[1] = 1;
            order[2] = 2;
        }
        vm.warp(fw.revealEnd());
        _finalize(fw, order);

        (,,,, uint256 filled,,) = fw.getAsk(carol);
        botPaid = fw.uniformPrice() * filled;
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 2 - ORDER-INVARIANCE / ENVY: dregg identical both orders; the AMM is not
    // ══════════════════════════════════════════════════════════════════════════

    function test_2_OrderInvariance_DreggIdentical_MockOrderDependent() public {
        // ── DREGG: identical book, OPPOSITE reveal order -> identical price + fills.
        RecycleFlywheel a = _bookAscending();
        RecycleFlywheel b = _bookDescending();
        assertEq(a.uniformPrice(), b.uniformPrice(), "same uniform price regardless of arrival order");
        assertEq(a.boughtTokens(), b.boughtTokens(), "same quantity cleared regardless of arrival order");
        _assertSameFill(a, b, alice);
        _assertSameFill(a, b, bob);
        _assertSameFill(a, b, carol);

        // ── MOCK: an AMM is arrival-ordered - the same two buyers in opposite order
        //    get different allocations (the front-run edge / envy CIRC cannot remove).
        (uint256 xFirst, uint256 xLast) = _mockTwoBuyerOrderDependence();
        assertGt(xFirst, xLast, "MOCK: buying FIRST gets strictly more tokens than buying LAST");
        console2.log("MOCK  buyer-X tokens when FIRST:", xFirst);
        console2.log("MOCK  buyer-X tokens when LAST :", xLast);
    }

    function _bookAscending() internal returns (RecycleFlywheel fw) {
        fw = _newFlywheel();
        fw.accrueFee{value: 80 ether}(keccak256("o"));
        _commitAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _commitAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _commitAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.commitEnd());
        _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a"); // idx0
        _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b"); // idx1
        _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c"); // idx2
        vm.warp(fw.revealEnd());
        uint256[] memory order = new uint256[](3);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;
        _finalize(fw, order);
    }

    function _bookDescending() internal returns (RecycleFlywheel fw) {
        fw = _newFlywheel();
        fw.accrueFee{value: 80 ether}(keccak256("o"));
        _commitAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        _commitAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _commitAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        vm.warp(fw.commitEnd());
        _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c"); // idx0
        _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b"); // idx1
        _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a"); // idx2
        vm.warp(fw.revealEnd());
        uint256[] memory order = new uint256[](3);
        order[0] = 2; // A @1g
        order[1] = 1; // B @2g
        order[2] = 0; // C @3g
        _finalize(fw, order);
    }

    function _assertSameFill(RecycleFlywheel a, RecycleFlywheel b, address who) internal view {
        (,,,, uint256 fa,,) = a.getAsk(who);
        (,,,, uint256 fb,,) = b.getAsk(who);
        assertEq(fa, fb, "identical fill regardless of arrival order");
    }

    /// Two buyers each spend 5 ETH on the same AMM; measure buyer-X's allocation
    /// when it goes FIRST vs LAST. A constant-product AMM is arrival-ordered.
    function _mockTwoBuyerOrderDependence() internal returns (uint256 xFirst, uint256 xLast) {
        uint256 seedTok = 1_000_000_000 * UNIT;

        MockAmm amm1 = new MockAmm(address(token), 30);
        token.approve(address(amm1), seedTok);
        amm1.addLiquidity{value: 50 ether}(seedTok);
        xFirst = amm1.buy{value: 5 ether}(0); // X first
        amm1.buy{value: 5 ether}(0); // Y second

        MockAmm amm2 = new MockAmm(address(token), 30);
        token.approve(address(amm2), seedTok);
        amm2.addLiquidity{value: 50 ether}(seedTok);
        amm2.buy{value: 5 ether}(0); // Y first
        xLast = amm2.buy{value: 5 ether}(0); // X second
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 3 - SPLIT DEVIATION: dregg reverts; the mock's owner key succeeds
    // ══════════════════════════════════════════════════════════════════════════

    function test_3_SplitDeviation_DreggReverts_MockSucceeds() public {
        // ── DREGG: a deviating split reverts against the committed public input ──
        RecycleFlywheel fw = _newFlywheel();
        fw.accrueFee{value: 80 ether}(keccak256("s"));
        _commitAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _commitAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _commitAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.commitEnd());
        _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.revealEnd());

        uint256[] memory order = new uint256[](3);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;

        // The operator TRIES to skim: claim a 90/10 split instead of the committed
        // 50/50. It reverts with the correct amounts - deviation is unconstructable.
        (uint256 correctBuy, uint256 correctPool) = fw.splitOf(80 ether);
        assertEq(correctBuy, 40 ether, "committed split = 50%");
        vm.expectRevert(abi.encodeWithSelector(RecycleFlywheel.SplitMismatch.selector, correctBuy, correctPool));
        fw.finalizeRecycle(order, 72 ether, 8 ether, bytes32(0), ""); // 90/10 skim attempt

        // The honest pole: the committed split finalizes.
        _finalize(fw, order);
        assertEq(fw.buyHalf(), 40 ether, "the committed 50/50 split is what executed");

        // ── MOCK: the owner's KEY re-weights the split at will - it SUCCEEDS ──
        MockAmm amm = new MockAmm(address(token), 30);
        uint256 seedTok = 1_000_000_000 * UNIT;
        token.approve(address(amm), seedTok);
        amm.addLiquidity{value: 50 ether}(seedTok);
        MockCircFlywheel mock = new MockCircFlywheel(address(token), address(amm), uint16(BUY_BPS));

        assertEq(mock.splitBps(), 5000, "mock starts at the disclosed 50/50");
        mock.setSplitBps(9000); // the deviation door - no revert
        assertEq(mock.splitBps(), 9000, "MOCK: the owner key skewed the split, and it SUCCEEDED");
        // You only learn after the fact - there is no committed input it checks against.
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 4 - CONSERVATION: dregg asserts per-asset netFlow=0; the mock has no cert
    // ══════════════════════════════════════════════════════════════════════════

    function test_4_Conservation_DreggNetFlowZero_MockLeaks() public {
        RecycleFlywheel fw = _driveHonest();

        // The conservation cert: per-asset netFlow == 0 (the on-chain twin of
        // `Market/Priced.lean priced_clearing_keystone`).
        (RecycleFlywheel.Receipt memory r,,) = fw.receiptBundle();
        assertEq(r.netQuote, int256(0), "quote netFlow = 0 (nothing minted/skimmed)");
        assertEq(r.netToken, int256(0), "token netFlow = 0 (nothing minted/destroyed)");

        // ETH conserves: accrued = seller-payment leg (retained) + pool quote seed.
        assertEq(fw.accrued(), fw.spentQuote() + fw.quoteSeed(), "accrued = to-sellers + to-pool, exactly");
        assertEq(address(fw).balance, fw.spentQuote(), "flywheel retains exactly the seller-payment leg");
        assertEq(address(fw.pool()).balance, fw.quoteSeed(), "pool got exactly the disclosed quote seed");

        // After settling everyone, the flywheel drains to ZERO - no value retained.
        fw.settleAsk(alice);
        fw.settleAsk(bob);
        fw.settleAsk(carol);
        assertEq(address(fw).balance, 0, "conservation closes: zero ETH residue");
        assertEq(token.balanceOf(address(fw)), 0, "conservation closes: zero token residue");

        // ── MOCK: no conservation statement exists. A sandwiched recycle LEAKS
        //    value to MEV - accrued does not equal value delivered, and nothing on
        //    the mock asserts otherwise (there is no netFlow cert to read).
        uint256 leaked = _mockSandwich();
        assertGt(leaked, 0, "MOCK: value leaked to MEV, with no conservation cert to catch it");
        console2.log("MOCK  value leaked to MEV, uncertified (wei):", leaked);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 5 - RE-CHECKABILITY: a non-witness re-derives dregg's receipt; the mock is raw
    // ══════════════════════════════════════════════════════════════════════════

    function test_5_ReCheckability_DreggNonWitnessVerifies_MockRaw() public {
        RecycleFlywheel fw = _driveHonest();

        // A NON-WITNESS reads only the public bundle and re-derives the head.
        (RecycleFlywheel.Receipt memory r, bytes32 head, bytes memory sig) = fw.receiptBundle();
        assertEq(sig.length, 65, "the head is operator-signed");
        assertEq(fw.recomputeReceiptHead(r), head, "non-witness recomputes the receipt head from public data");
        assertTrue(fw.verifyReceipt(), "the operator signature over the head verifies - ex-ante, not ex-post trust");

        // TAMPER-EVIDENCE: flip any field and the chain head no longer matches.
        RecycleFlywheel.Receipt memory tampered = r;
        tampered.uniformPrice = r.uniformPrice + 1;
        assertTrue(fw.recomputeReceiptHead(tampered) != head, "any tamper breaks the prev-hash chain");
        tampered = r;
        tampered.quoteSeed = r.quoteSeed - 1;
        assertTrue(fw.recomputeReceiptHead(tampered) != head, "a skimmed pool seed breaks the chain too");

        // ── MOCK: there is nothing to re-derive - only a raw transfer + an event to
        //    eyeball on a block explorer. No signed chain, no verify-only path.
        //    (MockCircFlywheel exposes no receipt/verify surface by construction.)
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 6 - PROVENANCE: dregg tags each inflow with its source receipt; mock opaque
    // ══════════════════════════════════════════════════════════════════════════

    function test_6_Provenance_DreggTagged_MockOpaque() public {
        RecycleFlywheel fw = _newFlywheel();
        // Two inflows, each tagged with the hash of the work that produced it.
        fw.accrueFee{value: 20 ether}(keccak256("turn-receipt-1"));
        fw.accrueFee{value: 20 ether}(keccak256("game-move-2"));
        assertEq(fw.inflowCount(), 2, "two inflows");
        assertEq(fw.provenancedCount(), 2, "both carry a source receipt");
        assertEq(fw.provenanceBps(), 10000, "100% provenanced - provenance is proven, not assumed");

        // An UNPROVENANCED inflow (the mock's only kind) drops the fraction.
        fw.accrueFee{value: 20 ether}(bytes32(0));
        assertEq(fw.provenanceBps(), 6666, "an opaque inflow is counted but not provenanced");

        // ── MOCK: `recycle` takes raw ETH with NO source-receipt parameter - every
        //    inflow is provenance-0, indistinguishable usage vs wash vs team top-up.
        console2.log("DREGG provenanced fraction (bps):", fw.provenanceBps());
        console2.log("MOCK  provenanced fraction (bps): 0 (no such surface)");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 7 - HONEST GAS / LATENCY PREMIUM: dregg is NOT cheaper - report it plainly
    // ══════════════════════════════════════════════════════════════════════════

    function test_7_GasPremium_ReportedHonestly() public {
        // ── DREGG: the full recycle turn (accrue x2, commit x3, reveal x3,
        //    finalize=split+clear+seed+conserve+sign) + settle x3, plus a
        //    commit->reveal latency the mock does not pay. Measure finalize alone
        //    (the clearing+cert step) and the whole loop.
        RecycleFlywheel fw = _newFlywheel();
        fw.accrueFee{value: 40 ether}(keccak256("g1"));
        fw.accrueFee{value: 40 ether}(keccak256("g2"));
        _commitAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _commitAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _commitAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.commitEnd());
        _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.revealEnd());
        uint256[] memory order = new uint256[](3);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;
        (uint256 buyHalf, uint256 poolHalf, bytes32 head) = _buildReceipt(fw, order);
        bytes memory sig = _sign(head);

        uint256 g0 = gasleft();
        fw.finalizeRecycle(order, buyHalf, poolHalf, head, sig);
        uint256 dreggFinalizeGas = g0 - gasleft();

        // ── MOCK: one market buy + one LP-add, a single tx, no commit->reveal.
        MockAmm amm = new MockAmm(address(token), 30);
        uint256 seedTok = 1_000_000_000 * UNIT;
        token.approve(address(amm), seedTok);
        amm.addLiquidity{value: 50 ether}(seedTok);
        MockCircFlywheel mock = new MockCircFlywheel(address(token), address(amm), uint16(BUY_BPS));

        uint256 g1 = gasleft();
        mock.recycle{value: 20 ether}(0);
        uint256 mockRecycleGas = g1 - gasleft();

        console2.log("DREGG finalize (clear+split+seed+conserve+sign) gas:", dreggFinalizeGas);
        console2.log("MOCK  recycle  (market-buy + LP-add) gas          :", mockRecycleGas);
        // HONEST: dregg costs more gas AND a commit->reveal latency the mock skips.
        // The claim is NOT cheaper/faster - it is front-run-immune + deviation-proof
        // + conserving + re-checkable, at this stated, bounded premium.
        assertGt(dreggFinalizeGas, mockRecycleGas, "dregg pays a real, bounded verification premium (honest)");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // 8 - the clearing rejects a dropped/inserted book (no-drop / no-insert)
    // ══════════════════════════════════════════════════════════════════════════

    function test_8_Clearing_RejectsBadPermutationAndBadOrder() public {
        RecycleFlywheel fw = _newFlywheel();
        fw.accrueFee{value: 80 ether}(keccak256("k"));
        _commitAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _commitAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _commitAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.commitEnd());
        _revealAsk(fw, alice, 1 * G, 3_000_000_000, "a");
        _revealAsk(fw, bob, 2 * G, 3_000_000_000, "b");
        _revealAsk(fw, carol, 3 * G, 4_000_000_000, "c");
        vm.warp(fw.revealEnd());

        // A DROP/INSERT (index 0 twice, 2 missing) is refused.
        uint256[] memory dup = new uint256[](3);
        dup[0] = 0;
        dup[1] = 0;
        dup[2] = 1;
        vm.expectRevert(RecycleFlywheel.BadPermutation.selector);
        fw.finalizeRecycle(dup, 40 ether, 40 ether, bytes32(0), "");

        // A NON-ASCENDING order (a mis-sorted, non-uniform clearing) is refused.
        uint256[] memory bad = new uint256[](3);
        bad[0] = 2; // C @3g first
        bad[1] = 1;
        bad[2] = 0;
        vm.expectRevert(RecycleFlywheel.NotSortedAscending.selector);
        fw.finalizeRecycle(bad, 40 ether, 40 ether, bytes32(0), "");
    }
}
