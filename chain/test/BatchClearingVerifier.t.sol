// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {BatchClearingVerifier} from "../contracts/launchpad/BatchClearingVerifier.sol";

/// Validates BatchClearingVerifier against the numeric reference
/// (/tmp/clearing_check3.py conservation + LVR-capture, /tmp/perm_check.py permutation
/// invariance incl. the marginal tie) and the adversarial polarity of each check.
///
/// Canonical fixture (from clearing_check3.py, base-unit / WAD scaled):
///   Rt=1000e18, Rq=2000e18, k=2e42, p*=2.2e18.
///   Curve pin ⇒ dt = 46537410754407684553  (= ⌊g(p*)⌋ base units, ≈46.537e18).
///   Marginal SELL at 2.2 rationed to x = 13462589245592315447 (approx 13.463e18).
///   Post-trade: newRt≈953.46e18, newRq≈2102.38e18, k'≈2.00454e42 > k (LVR captured).
contract BatchClearingVerifierTest is Test {
    BatchClearingVerifier v;

    uint256 constant WAD = 1e18;
    uint256 constant RT = 1000e18;
    uint256 constant RQ = 2000e18;
    uint256 constant P = 22e17; // 2.2e18
    uint256 constant DT = 46537410754407684553; // pinned ⌊g(p*)⌋
    uint256 constant XMARG = 13462589245592315447; // marginal SELL fill (6-order set)

    // distinct order identities (for the T2 fills-by-identity check)
    address constant A0 = address(0xA0);
    address constant A1 = address(0xA1);
    address constant A2 = address(0xA2);
    address constant A3 = address(0xA3);
    address constant A4 = address(0xA4);
    address constant A5 = address(0xA5);
    address constant A6 = address(0xA6);

    function setUp() public {
        v = new BatchClearingVerifier();
    }

    // ── canonical 6-order book (clearing_check3.py) ────────────────────────────────────
    function _orders6() internal pure returns (BatchClearingVerifier.Order[] memory o) {
        o = new BatchClearingVerifier.Order[](6);
        o[0] = BatchClearingVerifier.Order(true, 230e16, 100e18, A0); // BUY  2.30  100
        o[1] = BatchClearingVerifier.Order(true, 210e16, 80e18, A1); // BUY  2.10   80
        o[2] = BatchClearingVerifier.Order(true, 190e16, 50e18, A2); // BUY  1.90   50
        o[3] = BatchClearingVerifier.Order(false, 195e16, 40e18, A3); // SELL 1.95   40
        o[4] = BatchClearingVerifier.Order(false, 220e16, 30e18, A4); // SELL 2.20   30 (marginal)
        o[5] = BatchClearingVerifier.Order(false, 250e16, 60e18, A5); // SELL 2.50   60
    }

    function _fills6() internal pure returns (uint256[] memory f) {
        f = new uint256[](6);
        f[0] = 100e18; // BUY 2.30 fully filled (strictly in-money)
        f[1] = 0; // BUY 2.10 < p ⇒ out
        f[2] = 0; // BUY 1.90 < p ⇒ out
        f[3] = 40e18; // SELL 1.95 < p fully filled (strictly in-money)
        f[4] = XMARG; // SELL 2.20 == p marginal, pro-rata rationed
        f[5] = 0; // SELL 2.50 > p ⇒ out
    }

    function _reserves() internal pure returns (BatchClearingVerifier.Reserves memory) {
        // floors well below post-trade reserves (953e18 / 2102e18); fee reserved.
        return BatchClearingVerifier.Reserves(RT, RQ, 1e18, 1e18, 30);
    }

    function _clear6() internal pure returns (BatchClearingVerifier.Clear memory) {
        return BatchClearingVerifier.Clear(P, _fills6(), DT, true);
    }

    // ════════════════════════════════════════════════════════════════════════════════════
    // ACCEPT — the validated example
    // ════════════════════════════════════════════════════════════════════════════════════
    function test_Accept_ValidatedExample() public view {
        assertTrue(v.verifyClear(_orders6(), _reserves(), _clear6()));
    }

    /// Mirror the python asserts: conservation exact + k' >= k (LVR captured).
    function test_Accept_ConservationAndLvr() public pure {
        uint256 sumBuy = 100e18;
        uint256 sumSell = 40e18 + XMARG;
        assertEq(sumBuy - sumSell, DT, "token conservation: buyers == sellers + dt");

        // full-precision quote conservation (pool leg = p·dt), exact at uniform p:
        assertEq(P * sumBuy, P * sumSell + P * DT, "quote conservation at p (full precision)");
        uint256 quoteDelta = (P * DT) / WAD; // base-unit pool quote leg (floored, favor-pool)

        uint256 k = RT * RQ;
        uint256 newRt = RT - DT;
        uint256 newRq = RQ + quoteDelta;
        assertGe(newRt * newRq, k, "k' >= k (LVR non-decreasing)");
        assertGt(newRt * newRq, k, "k' strictly > k here (surplus captured)");
    }

    // ════════════════════════════════════════════════════════════════════════════════════
    // ADVERSARIAL REJECTS — one per test
    // ════════════════════════════════════════════════════════════════════════════════════

    /// Check 1 — wrong price: a BUY filled through its own limit (2.10 < p=2.2).
    function test_Reject_WrongPrice_FillThroughLimit() public {
        BatchClearingVerifier.Clear memory c = _clear6();
        c.fills[1] = 80e18; // BUY 2.10 gets filled though limit < p
        vm.expectRevert(abi.encodeWithSelector(BatchClearingVerifier.C1_WrongSide.selector, uint256(1)));
        v.verifyClear(_orders6(), _reserves(), c);
    }

    /// Check 2 — left-on-table: a strictly in-money BUY (2.30 > p) underfilled.
    function test_Reject_LeftOnTable() public {
        BatchClearingVerifier.Clear memory c = _clear6();
        c.fills[0] = 50e18; // half-fill the strictly-in-money buy
        vm.expectRevert(abi.encodeWithSelector(BatchClearingVerifier.C2_LeftOnTable.selector, uint256(0)));
        v.verifyClear(_orders6(), _reserves(), c);
    }

    /// Check 3 — non-conserving fills: marginal fill changed so imbalance != dt.
    function test_Reject_NonConserving() public {
        BatchClearingVerifier.Clear memory c = _clear6();
        c.fills[4] = 20e18; // still on-side & <= qty, but breaks Σbuy − Σsell == dt
        vm.expectRevert(BatchClearingVerifier.C3_Imbalance.selector);
        v.verifyClear(_orders6(), _reserves(), c);
    }

    /// Check 4 — dt violates the curve pin p·(Rt−dt)²==k (dt too SMALL ⇒ under-sell).
    /// Conservation is kept (marginal fill compensates) so the pin, not check 3, is the gate.
    function test_Reject_CurvePin_UnderSell() public {
        BatchClearingVerifier.Clear memory c = _clear6();
        c.dt = DT - 1e18; // pool under-sells g(p)
        c.fills[4] = XMARG + 1e18; // keep Σbuy − Σsell == dt
        vm.expectRevert(BatchClearingVerifier.C4_CurvePinHigh.selector);
        v.verifyClear(_orders6(), _reserves(), c);
    }

    /// Check 4 — a clear that would drop k' (LP-negative): pool OVER-sells past g(p).
    /// The sqrt-free pin catches it as CurvePinLow — i.e. no clear that over-sells (and would
    /// erode the pool's product) can pass. The k' >= k guard is defense-in-depth behind it.
    function test_Reject_LpNegative_OverSell() public {
        BatchClearingVerifier.Clear memory c = _clear6();
        c.dt = DT + 1e18; // pool over-sells g(p)
        c.fills[4] = XMARG - 1e18; // keep Σbuy − Σsell == dt
        vm.expectRevert(BatchClearingVerifier.C4_CurvePinLow.selector);
        v.verifyClear(_orders6(), _reserves(), c);
    }

    /// Check 4 — floor breach: raise the token floor above the post-trade reserve.
    function test_Reject_FloorBreach() public {
        BatchClearingVerifier.Reserves memory r = _reserves();
        r.ft = 990e18; // newRt ≈ 953e18 < 990e18
        vm.expectRevert(BatchClearingVerifier.C4_FloorToken.selector);
        v.verifyClear(_orders6(), r, _clear6());
    }

    /// Check 1 — over-qty: a fill exceeding the order's stated quantity.
    function test_Reject_OverQty() public {
        BatchClearingVerifier.Clear memory c = _clear6();
        c.fills[0] = 100e18 + 1; // > qty
        vm.expectRevert(abi.encodeWithSelector(BatchClearingVerifier.C1_OverQty.selector, uint256(0)));
        v.verifyClear(_orders6(), _reserves(), c);
    }

    // ════════════════════════════════════════════════════════════════════════════════════
    // PERMUTATION — T2 sanity at the Solidity level (perm_check.py: 7 orders, marginal TIE)
    // ════════════════════════════════════════════════════════════════════════════════════
    // Two SELLs at the marginal 2.20 (qty 30 and 15) split the residual pro-rata by qty:
    //   fill(30) = resid*30/45, fill(15) = resid*15/45, resid = 13462589245592315447.
    uint256 constant TIE_A = 8975059497061543631; // SELL 2.20 qty30 (marginal)
    uint256 constant TIE_B = 4487529748530771816; // SELL 2.20 qty15 (marginal)

    struct Keyed {
        address who;
        uint256 fill;
    }

    /// canonical 7-order book with the marginal tie, in a chosen base order.
    function _orders7() internal pure returns (BatchClearingVerifier.Order[] memory o) {
        o = new BatchClearingVerifier.Order[](7);
        o[0] = BatchClearingVerifier.Order(true, 230e16, 100e18, A0);
        o[1] = BatchClearingVerifier.Order(true, 210e16, 80e18, A1);
        o[2] = BatchClearingVerifier.Order(true, 190e16, 50e18, A2);
        o[3] = BatchClearingVerifier.Order(false, 195e16, 40e18, A3);
        o[4] = BatchClearingVerifier.Order(false, 220e16, 30e18, A4); // marginal tie #1
        o[5] = BatchClearingVerifier.Order(false, 220e16, 15e18, A5); // marginal tie #2
        o[6] = BatchClearingVerifier.Order(false, 250e16, 60e18, A6);
    }

    function _fills7() internal pure returns (uint256[] memory f) {
        f = new uint256[](7);
        f[0] = 100e18;
        f[1] = 0;
        f[2] = 0;
        f[3] = 40e18;
        f[4] = TIE_A;
        f[5] = TIE_B;
        f[6] = 0;
    }

    /// Apply a permutation `perm` to both orders and fills (identity-preserving), return both.
    function _permute(uint8[7] memory perm)
        internal
        pure
        returns (BatchClearingVerifier.Order[] memory o, uint256[] memory f)
    {
        BatchClearingVerifier.Order[] memory base = _orders7();
        uint256[] memory bf = _fills7();
        o = new BatchClearingVerifier.Order[](7);
        f = new uint256[](7);
        for (uint256 i = 0; i < 7; i++) {
            o[i] = base[perm[i]];
            f[i] = bf[perm[i]];
        }
    }

    function _expectedFillFor(address who) internal pure returns (uint256) {
        if (who == A0) return 100e18;
        if (who == A3) return 40e18;
        if (who == A4) return TIE_A;
        if (who == A5) return TIE_B;
        return 0; // A1, A2, A6
    }

    /// The base 7-order clear accepts, and each order's fill matches its identity fill.
    function test_Perm_BaseAccepts() public view {
        BatchClearingVerifier.Order[] memory o = _orders7();
        uint256[] memory f = _fills7();
        BatchClearingVerifier.Clear memory c = BatchClearingVerifier.Clear(P, f, DT, true);
        assertTrue(v.verifyClear(o, _reserves(), c));
        for (uint256 i = 0; i < 7; i++) {
            assertEq(f[i], _expectedFillFor(o[i].who), "fill keyed to identity");
        }
    }

    /// Several permutations: same ACCEPT + same fills-by-identity (T2 at Solidity level).
    function test_Perm_Invariance() public view {
        uint8[7][4] memory perms = [
            [uint8(6), 5, 4, 3, 2, 1, 0], // reversed
            [uint8(4), 5, 0, 6, 1, 3, 2], // tie-first scramble
            [uint8(3), 0, 6, 4, 2, 5, 1], // arbitrary
            [uint8(0), 1, 2, 3, 5, 4, 6] // swap the two tied marginals
        ];
        for (uint256 pI = 0; pI < 4; pI++) {
            (BatchClearingVerifier.Order[] memory o, uint256[] memory f) = _permute(perms[pI]);
            BatchClearingVerifier.Clear memory c = BatchClearingVerifier.Clear(P, f, DT, true);
            assertTrue(v.verifyClear(o, _reserves(), c), "permuted clear still accepts");
            for (uint256 i = 0; i < 7; i++) {
                assertEq(f[i], _expectedFillFor(o[i].who), "fill still keyed to identity");
            }
        }
    }
}
