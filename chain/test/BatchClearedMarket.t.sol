// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {BatchClearingVerifier} from "../contracts/launchpad/BatchClearingVerifier.sol";
import {BatchClearedMarket} from "../contracts/launchpad/BatchClearedMarket.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {MockStockToken} from "../contracts/launchpad/MockStockToken.sol";

/// The tangible Rung-3 demo: launch a coin, seed a coin/mNVDA batch-cleared market
/// (graduation), collect a real batch of coin/stock orders, a PERMISSIONLESS solver
/// submits a valid clear → the VERIFIED `verifyClear` accepts → settlement moves the
/// right coin + mNVDA at the single uniform price, reserves update, k′≥k (LVR
/// captured), balances conserve. Adversarial clears revert with no movement, and a
/// settled batch cannot be double-settled.
///
/// The order book is the canonical fixture the verifier test already validates
/// (clearing_check3.py): Rt=1000e18, Rq=2000e18, p*=2.2e18, dt pinned.
contract BatchClearedMarketTest is Test {
    BatchClearingVerifier verifier;
    BatchClearedMarket market;
    DreggLaunchToken coin;
    MockStockToken stock;

    uint256 constant WAD = 1e18;
    uint256 constant CAP = 10000e18;
    uint256 constant SEED_COIN = 1000e18; // Rt
    uint256 constant SEED_STOCK = 2000e18; // Rq
    uint256 constant FLOOR = 1e18;
    uint16 constant FEE = 30;

    // canonical clear (from clearing_check3.py / BatchClearingVerifier.t.sol)
    uint256 constant P = 22e17; // 2.2e18
    uint256 constant DT = 46537410754407684553; // ⌊g(p*)⌋
    uint256 constant XMARG = 13462589245592315447; // marginal SELL 2.20 fill

    // derived settlement amounts (favor-pool base-unit rounding)
    uint256 constant PAY0 = 220e18; // ceil(p·100)  — BUY 2.30 pays
    uint256 constant RECV3 = 88e18; // floor(p·40)  — SELL 1.95 receives
    uint256 constant RECV4 = 29617696340303093983; // floor(p·XMARG) — marginal SELL receives
    uint256 constant REFUND4 = 16537410754407684553; // 30e18 − XMARG coin back
    uint256 constant NEW_RT = 953462589245592315447; // Rt − dt
    uint256 constant NEW_RQ = 2102382303659696906017; // Rq + (Σpay − Σrecv)

    // buyer stock escrows (ceil(limit·qty/WAD))
    uint256 constant ESC0 = 230e18; // 2.30·100
    uint256 constant ESC1 = 168e18; // 2.10·80
    uint256 constant ESC2 = 95e18; // 1.90·50

    // actors
    address constant A0 = address(0xB0); // BUY 2.30 100
    address constant A1 = address(0xB1); // BUY 2.10  80
    address constant A2 = address(0xB2); // BUY 1.90  50
    address constant A3 = address(0xB3); // SELL 1.95 40
    address constant A4 = address(0xB4); // SELL 2.20 30 (marginal)
    address constant A5 = address(0xB5); // SELL 2.50 60
    address constant SOLVER = address(0x5011E7); // permissionless solver
    address constant SOLVER2 = address(0x5012E8); // a second, competing solver

    function setUp() public {
        verifier = new BatchClearingVerifier();
        // This test contract acts as the launchpad/graduation: it mints the coin
        // supply and seeds the market.
        coin = new DreggLaunchToken("Dregg Coin", "DREGG", CAP, address(this));
        coin.mint(address(this), CAP);
        stock = new MockStockToken("Mock NVDA", "mNVDA");

        market = new BatchClearedMarket(address(coin), address(stock), address(verifier));

        // ── Graduation: seed the coin/stock pool once ────────────────────────────
        stock.mint(address(this), SEED_STOCK);
        coin.approve(address(market), SEED_COIN);
        stock.approve(address(market), SEED_STOCK);
        market.seedFromGraduation(SEED_COIN, SEED_STOCK, FLOOR, FLOOR, FEE);
    }

    // ── fund an actor + submit an order into the open batch ──────────────────────
    function _buy(address who, uint256 escrow, uint256 limit, uint256 qty) internal {
        stock.mint(who, escrow);
        vm.startPrank(who);
        stock.approve(address(market), escrow);
        market.submitBuy(limit, qty);
        vm.stopPrank();
    }

    function _sell(address who, uint256 limit, uint256 qty) internal {
        coin.transfer(who, qty); // escrow is qty coin
        vm.startPrank(who);
        coin.approve(address(market), qty);
        market.submitSell(limit, qty);
        vm.stopPrank();
    }

    /// Submit the canonical 6-order book IN ORDER (fills are positional).
    function _submitBatch() internal {
        _buy(A0, ESC0, 230e16, 100e18);
        _buy(A1, ESC1, 210e16, 80e18);
        _buy(A2, ESC2, 190e16, 50e18);
        _sell(A3, 195e16, 40e18);
        _sell(A4, 220e16, 30e18);
        _sell(A5, 250e16, 60e18);
    }

    function _validClear() internal pure returns (BatchClearingVerifier.Clear memory) {
        uint256[] memory f = new uint256[](6);
        f[0] = 100e18;
        f[1] = 0;
        f[2] = 0;
        f[3] = 40e18;
        f[4] = XMARG;
        f[5] = 0;
        return BatchClearingVerifier.Clear(P, f, DT, true);
    }

    // ════════════════════════════════════════════════════════════════════════════
    // HAPPY PATH — launch → seed(graduate) → batch → permissionless clear → settle
    // ════════════════════════════════════════════════════════════════════════════
    function test_E2E_LaunchTradeGraduate() public {
        // seeded reserves match the launch proceeds
        (uint256 rt0, uint256 rq0) = market.reserves();
        assertEq(rt0, SEED_COIN, "seed Rt");
        assertEq(rq0, SEED_STOCK, "seed Rq");

        _submitBatch();
        assertEq(market.batchLength(0), 6, "batch collected 6 orders");

        // A permissionless solver settles the open batch.
        vm.prank(SOLVER);
        market.settle(0, _validClear());

        // ── reserves updated exactly ─────────────────────────────────────────────
        (uint256 rt1, uint256 rq1) = market.reserves();
        assertEq(rt1, NEW_RT, "Rt' = Rt - dt");
        assertEq(rq1, NEW_RQ, "Rq' = Rq + (Sigma pay - Sigma recv)");

        // k' >= k (LVR captured) and strictly greater here
        assertGe(rt1 * rq1, SEED_COIN * SEED_STOCK, "k' >= k");
        assertGt(rt1 * rq1, SEED_COIN * SEED_STOCK, "k' strictly > k (surplus captured)");

        // favor-pool: settled quote reserve DOMINATES the verifier's floored model
        uint256 quoteDeltaModel = (P * DT) / WAD; // what verifyClear credited the pool leg
        assertGe(rq1 - SEED_STOCK, quoteDeltaModel, "pool credited >= floor(p*dt/WAD)");

        // ── per-actor settlement (uniform price p*, favor-pool rounding) ──────────
        // A0 BUY fully filled: 100 coin in, 10 stock refunded (230 escrow - 220 paid)
        assertEq(coin.balanceOf(A0), 100e18, "A0 receives 100 coin");
        assertEq(stock.balanceOf(A0), ESC0 - PAY0, "A0 stock refund (10)");
        // A1, A2 out-of-money: full stock escrow refunded, no coin
        assertEq(stock.balanceOf(A1), ESC1, "A1 full refund");
        assertEq(coin.balanceOf(A1), 0, "A1 no coin");
        assertEq(stock.balanceOf(A2), ESC2, "A2 full refund");
        // A3 SELL fully filled: 40 coin gone, 88 stock received
        assertEq(coin.balanceOf(A3), 0, "A3 coin fully sold");
        assertEq(stock.balanceOf(A3), RECV3, "A3 receives 88 stock");
        // A4 marginal SELL: XMARG coin sold (refund the rest), floor(p*XMARG) stock in
        assertEq(coin.balanceOf(A4), REFUND4, "A4 unfilled coin refund");
        assertEq(stock.balanceOf(A4), RECV4, "A4 marginal stock receipt");
        // A5 out-of-money SELL: full coin refund
        assertEq(coin.balanceOf(A5), 60e18, "A5 full coin refund");
        assertEq(stock.balanceOf(A5), 0, "A5 no stock");

        // ── market's tracked reserves equal its real balances (no untracked dust) ─
        assertEq(coin.balanceOf(address(market)), rt1, "coin balance == reserveToken");
        assertEq(stock.balanceOf(address(market)), rq1, "stock balance == reserveQuote");

        // ── global conservation (closed system) ──────────────────────────────────
        _assertConserved();

        // batch is now settled and closed; the next batch is open
        assertTrue(market.settled(0), "batch 0 settled");
        assertEq(market.currentBatch(), 1, "next batch opened");
    }

    /// Total coin == CAP and total stock == everything minted — nothing created/destroyed.
    function _assertConserved() internal view {
        uint256 coinSum = coin.balanceOf(address(this)) + coin.balanceOf(address(market)) + coin.balanceOf(A0)
            + coin.balanceOf(A1) + coin.balanceOf(A2) + coin.balanceOf(A3) + coin.balanceOf(A4) + coin.balanceOf(A5);
        assertEq(coinSum, CAP, "coin conserved (== cap)");

        uint256 mintedStock = SEED_STOCK + ESC0 + ESC1 + ESC2; // all mNVDA ever minted
        uint256 stockSum = stock.balanceOf(address(this)) + stock.balanceOf(address(market)) + stock.balanceOf(A0)
            + stock.balanceOf(A1) + stock.balanceOf(A2) + stock.balanceOf(A3) + stock.balanceOf(A4)
            + stock.balanceOf(A5);
        assertEq(stockSum, mintedStock, "stock conserved");
    }

    // ════════════════════════════════════════════════════════════════════════════
    // ADVERSARIAL — a clear verifyClear rejects reverts settlement, moves nothing
    // ════════════════════════════════════════════════════════════════════════════

    /// Wrong price: fill an out-of-money BUY through its own limit (2.10 < p=2.2).
    function test_Adversarial_WrongPrice_Reverts() public {
        _submitBatch();
        BatchClearingVerifier.Clear memory bad = _validClear();
        bad.fills[1] = 80e18; // BUY 2.10 filled though limit < p

        _snapshotAndExpectNoMove();
        vm.prank(SOLVER);
        vm.expectRevert(abi.encodeWithSelector(BatchClearingVerifier.C1_WrongSide.selector, uint256(1)));
        market.settle(0, bad);
        _assertNoMove();
    }

    /// Non-conserving: change the marginal fill so imbalance != dt.
    function test_Adversarial_NonConserving_Reverts() public {
        _submitBatch();
        BatchClearingVerifier.Clear memory bad = _validClear();
        bad.fills[4] = 20e18; // still on-side & <= qty, but breaks Sigma buy - Sigma sell == dt

        _snapshotAndExpectNoMove();
        vm.prank(SOLVER);
        vm.expectRevert(BatchClearingVerifier.C3_Imbalance.selector);
        market.settle(0, bad);
        _assertNoMove();
    }

    /// Floor breach: submit against a market whose floor exceeds the post-trade Rt.
    function test_Adversarial_FloorBreach_Reverts() public {
        // fresh market with a token floor above NEW_RT
        BatchClearedMarket m2 = new BatchClearedMarket(address(coin), address(stock), address(verifier));
        stock.mint(address(this), SEED_STOCK);
        coin.approve(address(m2), SEED_COIN);
        stock.approve(address(m2), SEED_STOCK);
        m2.seedFromGraduation(SEED_COIN, SEED_STOCK, 990e18, FLOOR, FEE); // ft = 990 > 953

        // submit the batch into m2
        _buyTo(m2, A0, ESC0, 230e16, 100e18);
        _buyTo(m2, A1, ESC1, 210e16, 80e18);
        _buyTo(m2, A2, ESC2, 190e16, 50e18);
        _sellTo(m2, A3, 195e16, 40e18);
        _sellTo(m2, A4, 220e16, 30e18);
        _sellTo(m2, A5, 250e16, 60e18);

        vm.prank(SOLVER);
        vm.expectRevert(BatchClearingVerifier.C4_FloorToken.selector);
        m2.settle(0, _validClear());
        // no settlement
        assertFalse(m2.settled(0), "floor-breaching clear did not settle");
    }

    // ════════════════════════════════════════════════════════════════════════════
    // PERMISSIONLESS — two solvers race; valid one settles; no double-settle
    // ════════════════════════════════════════════════════════════════════════════
    function test_Permissionless_RaceAndNoDoubleSettle() public {
        _submitBatch();

        // Solver #1 submits an INVALID clear → reverts, no state change.
        BatchClearingVerifier.Clear memory bad = _validClear();
        bad.fills[0] = 50e18; // strictly in-money BUY underfilled ⇒ C2
        vm.prank(SOLVER);
        vm.expectRevert(abi.encodeWithSelector(BatchClearingVerifier.C2_LeftOnTable.selector, uint256(0)));
        market.settle(0, bad);
        assertFalse(market.settled(0), "invalid clear did not settle");

        // Solver #2 (a DIFFERENT address) submits the VALID clear → settles.
        vm.prank(SOLVER2);
        market.settle(0, _validClear());
        assertTrue(market.settled(0), "valid clear from a second solver settled");

        // Any further attempt to settle the same batch reverts (no double-settle).
        vm.prank(SOLVER);
        vm.expectRevert(abi.encodeWithSelector(BatchClearedMarket.AlreadySettled.selector, uint256(0)));
        market.settle(0, _validClear());

        vm.prank(SOLVER2);
        vm.expectRevert(abi.encodeWithSelector(BatchClearedMarket.AlreadySettled.selector, uint256(0)));
        market.settle(0, _validClear());
    }

    // ── helpers for the alternate-market adversarial case ────────────────────────
    function _buyTo(BatchClearedMarket m, address who, uint256 escrow, uint256 limit, uint256 qty) internal {
        stock.mint(who, escrow);
        vm.startPrank(who);
        stock.approve(address(m), escrow);
        m.submitBuy(limit, qty);
        vm.stopPrank();
    }

    function _sellTo(BatchClearedMarket m, address who, uint256 limit, uint256 qty) internal {
        coin.transfer(who, qty);
        vm.startPrank(who);
        coin.approve(address(m), qty);
        m.submitSell(limit, qty);
        vm.stopPrank();
    }

    // ── no-move snapshot for adversarial reverts ─────────────────────────────────
    uint256 private _rtSnap;
    uint256 private _rqSnap;
    uint256 private _mCoinSnap;
    uint256 private _mStockSnap;

    function _snapshotAndExpectNoMove() internal {
        (_rtSnap, _rqSnap) = market.reserves();
        _mCoinSnap = coin.balanceOf(address(market));
        _mStockSnap = stock.balanceOf(address(market));
    }

    function _assertNoMove() internal view {
        (uint256 rt, uint256 rq) = market.reserves();
        assertEq(rt, _rtSnap, "reserveToken unchanged after reject");
        assertEq(rq, _rqSnap, "reserveQuote unchanged after reject");
        assertEq(coin.balanceOf(address(market)), _mCoinSnap, "market coin unchanged");
        assertEq(stock.balanceOf(address(market)), _mStockSnap, "market stock unchanged");
        assertFalse(market.settled(0), "batch not settled after reject");
    }
}
