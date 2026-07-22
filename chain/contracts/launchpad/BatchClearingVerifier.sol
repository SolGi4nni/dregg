// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title BatchClearingVerifier — the on-chain predicate for a uniform-price batch clear.
///
/// Rung 2a of the fair market. The contract does NOT compute the clear (expensive); a
/// permissionless solver submits a candidate `(p, fills[], dt, poolSells)` and this pure
/// predicate accepts/rejects it in O(n) integer checks. The theorems T1,T3,T4,T4',T5 are
/// stated about the *verified* result, so they hold for whatever a solver submits — no
/// trust in the solver.
///
/// Substrate note: this is HAND-WRITTEN EVM Solidity — the launchpad surface that
/// Lean/Verifereum verifies as *bytecode*. It is NOT a dregg Lean AIR. It is authored to
/// be minimal and provable (few branches, all O(n), no external calls, no on-chain sqrt).
///
/// Spec: docs/deos/CLEARING-FUNCTION-SPEC.md (checks 1–6, theorems T1–T6).
/// Numeric reference (validates the math): /tmp/clearing_check3.py, /tmp/perm_check.py.
///
/// ─────────────────────────────────────────────────────────────────────────────────────
/// FIXED-POINT CONVENTION (get this exactly right — it is the sharp edge)
/// ─────────────────────────────────────────────────────────────────────────────────────
///  WAD = 1e18.
///  • `limit`, `p`  : quote-per-token, WAD-scaled. A price of 2.2 quote/token is 2.2e18.
///  • `qty`, `fills[i]`, `dt`, `Rt`, `Rq`, `ft`, `fq` : *base units* (raw integers).
///  • A quote amount for `q` base-unit tokens at price `p` is  `p * q / WAD`  (base-unit
///    quote). The single division by WAD is where price (WAD) meets a base-unit quantity.
///
///  Curve pin (check 4), sqrt-free. The pool is a price-taker willing to sell g(p) tokens
///  to bring its curve-marginal up to p:  p·(Rt−dt)² = k  with k = Rt·Rq. In real units
///  that identity is dimensionless-consistent; in our scaling `p` carries a WAD, so the
///  emitted integer polynomial is
///
///        f(dt) := p * (Rt − dt)² / WAD     (net-buy;  Rt+dt for net-sell)
///
///  and the pin is  f(dt) == k  with k = Rt·Rq. Derivation of the lone /WAD: with p_wad =
///  p·WAD and reserves in base units, p_wad·(Rt−dt)²/WAD = p·(Rt−dt)²·WAD² and k = Rt·Rq·
///  (base²) — the WAD on p exactly cancels one WAD of the squared base-unit reserve. (Checked
///  against the validated model: Rt=1000e18,Rq=2000e18,p=2.2e18 ⇒ dt=46.537…e18.)
///
/// ─────────────────────────────────────────────────────────────────────────────────────
/// ROUNDING (favor-the-pool, sqrt-free, tolerance-free)
/// ─────────────────────────────────────────────────────────────────────────────────────
///  g(p) is irrational, so no integer `dt` makes f(dt) == k exactly. Instead of a magic
///  tolerance constant we PIN `dt` by integer bracketing:
///
///        f(dt) >= k   AND   f(dt + 1) < k
///
///  f is strictly decreasing in dt, so exactly one integer satisfies this: dt = ⌊root⌋
///  where root solves f=k. This is the largest dt for which the pool's post-curve product
///  still dominates k — i.e. the pool sells at most g(p) tokens, never more (favor-the-pool:
///  the pool never over-sells past its price-taker willingness). The residual sub-wei is
///  absorbed by the marginal order's pro-rata fill; conservation (check 5) is then asserted
///  EXACTLY on the submitted integers, so no value is created. The effective tolerance is
///  one wei of `dt`, and it is safe because the two real guarantees — k′ ≥ k (check 4b) and
///  the floors — are checked as EXACT integer inequalities on top of the pin.
contract BatchClearingVerifier {
    uint256 internal constant WAD = 1e18;

    struct Order {
        bool isBuy; // true = BUY (pays quote for tokens), false = SELL
        uint256 limit; // quote-per-token, WAD
        uint256 qty; // token base units the order offers/wants
        address who; // order identity (used off-chain / by settlement; T2 keys fills to it)
    }

    struct Reserves {
        uint256 Rt; // pool token reserve, base units
        uint256 Rq; // pool quote reserve, base units
        uint256 ft; // token floor
        uint256 fq; // quote floor
        uint16 feeBps; // pool fee (bps) — LP revenue on the pool leg; reserved (see note)
    }

    struct Clear {
        uint256 p; // uniform clearing price, WAD
        uint256[] fills; // per-order filled quantity, base units, positionally aligned to orders
        uint256 dt; // pool token delta magnitude, base units
        bool poolSells; // true: net buy pressure ⇒ pool SELLS dt (net-buy); false: pool BUYS
    }

    error LengthMismatch();
    error C1_WrongSide(uint256 i); // fill on the wrong side of its limit
    error C1_OverQty(uint256 i); // fill exceeds the order's qty
    error C2_LeftOnTable(uint256 i); // strictly in-money order not fully filled
    error C3_Imbalance(); // net order imbalance != dt (also = token conservation)
    error C4_CurvePinLow(); // f(dt) < k: pool would sell more than g(p)
    error C4_CurvePinHigh(); // f(dt+1) >= k: dt too small, pool under-sells g(p)
    error C4_LpNegative(); // k' < k: LP would lose (LVR not captured)
    error C4_FloorToken(); // post-trade token reserve < floor
    error C4_FloorQuote(); // post-trade quote reserve < floor
    error C5_QuoteConservation(); // quote legs at p do not sum to zero

    /// @notice Reverts with a typed reason on any failed check; returns true iff the
    ///         candidate clear satisfies all of checks 1–6. Pure, O(n), no external calls.
    function verifyClear(
        Order[] calldata orders,
        Reserves calldata r,
        Clear calldata c
    ) public pure returns (bool) {
        uint256 n = orders.length;
        if (c.fills.length != n) revert LengthMismatch();

        uint256 sumBuy; // Σ BUY fills   (base units)
        uint256 sumSell; // Σ SELL fills  (base units)

        // ── Checks 1 & 2 (per order, O(n)) ──────────────────────────────────────────────
        for (uint256 i = 0; i < n; i++) {
            Order calldata o = orders[i];
            uint256 fill = c.fills[i];

            // Check 1 — within-qty (applies to every order incl. zero fills).
            if (fill > o.qty) revert C1_OverQty(i);

            if (fill > 0) {
                // Check 1 — right-side: no order trades through its own limit.
                //   BUY fills only if limit >= p ; SELL fills only if limit <= p.
                if (o.isBuy) {
                    if (o.limit < c.p) revert C1_WrongSide(i);
                    sumBuy += fill;
                } else {
                    if (o.limit > c.p) revert C1_WrongSide(i);
                    sumSell += fill;
                }
            }

            // Check 2 — no-left-on-table: every STRICTLY in-money order is fully filled;
            // only orders at exactly the marginal level (limit == p) may be partial.
            //   BUY strictly in-money  ⇔ limit >  p
            //   SELL strictly in-money ⇔ limit <  p
            bool strictInMoney = o.isBuy ? (o.limit > c.p) : (o.limit < c.p);
            if (strictInMoney && fill != o.qty) revert C2_LeftOnTable(i);
        }

        // ── Check 3 — imbalance = pool delta (also = token conservation, check 5 token leg) ─
        //   poolSells (net-buy):  Σbuy − Σsell == dt   (pool provides dt tokens)
        //   else       (net-sell): Σsell − Σbuy == dt   (pool absorbs dt tokens)
        if (c.poolSells) {
            if (sumBuy < sumSell || sumBuy - sumSell != c.dt) revert C3_Imbalance();
        } else {
            if (sumSell < sumBuy || sumSell - sumBuy != c.dt) revert C3_Imbalance();
        }

        // ── Check 4 — pool price-taker + solvent + LP-positive (SQRT-FREE) ───────────────
        uint256 k = r.Rt * r.Rq;
        uint256 newRt;
        uint256 newRq;
        uint256 quoteDelta = (c.p * c.dt) / WAD; // pool quote leg at the UNIFORM price p

        if (c.poolSells) {
            // net-buy: pool sells dt tokens, receives quoteDelta quote.
            uint256 rem = r.Rt - c.dt; // Rt − dt  (reverts on underflow ⇒ pool can't sell past empty)
            newRt = rem;
            newRq = r.Rq + quoteDelta;
            // Curve pin (bracket): f(dt) >= k > f(dt+1), f(dt) = p·(Rt−dt)²/WAD.
            if ((c.p * (rem * rem)) / WAD < k) revert C4_CurvePinLow();
            uint256 remUp = rem - 1; // Rt − (dt+1)
            if ((c.p * (remUp * remUp)) / WAD >= k) revert C4_CurvePinHigh();
        } else {
            // net-sell: pool buys dt tokens, pays quoteDelta quote.
            uint256 rem = r.Rt + c.dt; // Rt + dt
            newRt = rem;
            if (r.Rq < quoteDelta) revert C4_FloorQuote(); // pool cannot pay more quote than it holds
            newRq = r.Rq - quoteDelta;
            // Curve pin (bracket): f(dt) >= k > f(dt+1), f(dt) = p·(Rt+dt)²/WAD.
            if ((c.p * (rem * rem)) / WAD < k) revert C4_CurvePinLow();
            uint256 remUp = rem + 1; // Rt + (dt+1)
            if ((c.p * (remUp * remUp)) / WAD >= k) revert C4_CurvePinHigh();
        }

        // Check 4b — LP-positive: k' = newRt·newRq is NON-decreasing (LVR captured for LPs).
        if (newRt * newRq < k) revert C4_LpNegative();
        // Check 4c — solvency floors (exact integer inequalities).
        if (newRt < r.ft) revert C4_FloorToken();
        if (newRq < r.fq) revert C4_FloorQuote();

        // ── Checks 5 & 6 — conservation (Σδ = 0 per asset), every leg at the single p ────
        //   Token leg conserves ⇔ check 3 (already asserted).
        //   Quote leg: quote paid by buyers == quote to sellers + the pool's quote.
        //   Every leg is priced at the SINGLE uniform p (check 6, uniform price): buyer pays
        //   p·fill, seller receives p·fill, pool takes p·dt. We assert the identity at FULL
        //   PRECISION (before the /WAD to base-unit quote) so it is EXACT and free of
        //   per-leg floor drift:  p·Σbuy == p·Σsell + p·dt. Because every leg carries the
        //   SAME p, this reduces to Σbuy == Σsell + dt (check 3) — that reduction IS the
        //   content of "uniform price ⇒ quote conserves". Splitting each aggregate into
        //   base-unit quote (÷WAD) and rounding per order is deferred to the settlement
        //   wrapper, where the residual wei rounds toward the POOL (favor-the-pool); the
        //   pool's `quoteDelta` above is floored, which UNDER-states its gain, so the k′≥k
        //   and floor checks are conservative w.r.t. that later rounding. No p·x overflows:
        //   they equal p·(the token aggregates) already bounded by check 4's domain.
        if (c.poolSells) {
            // buyers pay sellers + pool
            if (c.p * sumBuy != c.p * sumSell + c.p * c.dt) revert C5_QuoteConservation();
        } else {
            // pool + buyers pay sellers  (pool is a net buyer of tokens ⇒ it pays quote)
            if (c.p * sumBuy + c.p * c.dt != c.p * sumSell) revert C5_QuoteConservation();
        }

        return true;
    }
}
