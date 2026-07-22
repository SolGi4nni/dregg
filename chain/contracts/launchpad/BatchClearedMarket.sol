// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {BatchClearingVerifier} from "./BatchClearingVerifier.sol";

/// The minimal ERC-20 surface both legs (the launched coin + the mock stock)
/// share. transfer/transferFrom return `true` on success or revert.
interface IErc20Leg {
    function transfer(address to, uint256 value) external returns (bool);
    function transferFrom(address from, address to, uint256 value) external returns (bool);
    function balanceOf(address who) external view returns (uint256);
}

/// @title BatchClearedMarket — the permissionless coin/stock batch-cleared market.
///
/// Rung 3 of the fair market (`docs/deos/FAIR-BATCH-MARKET-DESIGN.md`). A coin
/// (`DreggLaunchToken`) trades against a stock token (`MockStockToken`, the QUOTE)
/// at a single **uniform price per batch**, cleared by a permissionless solver and
/// checked by the VERIFIED core `BatchClearingVerifier.verifyClear` — the exact same
/// predicate the launch uses. Graduation seeds this pool once; from then on the pair
/// trades per block through the identical clear.
///
/// ## What this contract is (and is NOT)
/// - It is the SETTLEMENT WRAPPER around the verified predicate. It does NOT
///   re-implement clearing — it collects a batch of escrowed orders, hands them
///   (with the live reserves) to `verifyClear`, and SETTLES iff that returns true.
/// - There is NO admin, NO privileged solver, NO role. Anyone submits an order,
///   anyone submits a clear; a clear that `verifyClear` rejects reverts with no
///   state change, and a batch settles at most once.
///
/// ## The seal is plaintext (rung-1 MVP)
/// Orders are submitted in the CLEAR and escrowed in a per-batch mapping. This is
/// the honest MVP: it is front-runnable at the mempool the way any plaintext order
/// is, because the SEAL (commit→reveal, then fhegg threshold decryption) is a later
/// rung, deliberately a module and not entangled with the clearing core. What is
/// already fair here is the CLEAR: every filled order in a batch gets the one
/// uniform price, independent of its position (T1/T2 over the verified predicate).
///
/// ## Honest assurance scope
/// This contract is RUNNABLE and forge-tested, NOT yet proven over its bytecode —
/// the Verifereum refinement is the parallel track. `verifyClear`'s checks 1–6 are
/// the load-bearing invariant; this wrapper ADDS the per-order base-unit rounding
/// (deferred from the verifier) and the ERC-20 movement, and is trusted to (a) pass
/// the true live reserves + the true stored batch to `verifyClear`, and (b) round
/// every split toward the POOL so the settled reserves DOMINATE the verified model
/// (see `settle`). Those two are the wrapper's assumptions; everything the verifier
/// checks (uniform price, conservation, solvency floor, k′≥k) it checks exactly.
contract BatchClearedMarket {
    uint256 internal constant WAD = 1e18;

    /// The launched coin — the TOKEN reserve leg (`Rt`).
    IErc20Leg public immutable coin;
    /// The stock token (mNVDA) — the QUOTE reserve leg (`Rq`).
    IErc20Leg public immutable stock;
    /// The VERIFIED clearing predicate. Stateless/pure; reused, never reimplemented.
    BatchClearingVerifier public immutable verifier;

    // ─── Live pool reserves (tracked internally, not via balanceOf, so a token
    //     donation can never move the price or the solvency accounting) ──────────
    uint256 public reserveToken; // Rt, coin base units
    uint256 public reserveQuote; // Rq, stock base units
    uint256 public floorToken; // ft
    uint256 public floorQuote; // fq
    uint16 public feeBps;
    bool public seeded;

    // ─── Batches ────────────────────────────────────────────────────────────────
    /// The single OPEN batch orders are collected into. `settle` clears it and opens
    /// the next (per-block cadence: one batch, then the next).
    uint256 public currentBatch;

    /// A stored order + the inputs the trader ESCROWED at submit (so settlement can
    /// always move funds without a re-approval race — the plaintext-MVP honesty).
    struct StoredOrder {
        bool isBuy;
        uint256 limit; // quote-per-token, WAD
        uint256 qty; // coin base units
        address who;
        uint256 escrow; // BUY: stock escrowed (ceil(limit·qty/WAD)); SELL: coin escrowed (qty)
    }

    mapping(uint256 => StoredOrder[]) internal batchOrders;
    mapping(uint256 => bool) public settled;

    // ─── Events ───────────────────────────────────────────────────────────────
    event Seeded(uint256 reserveToken, uint256 reserveQuote, uint256 floorToken, uint256 floorQuote, uint16 feeBps);
    event OrderSubmitted(
        uint256 indexed batchId, uint256 indexed index, address indexed who, bool isBuy, uint256 limit, uint256 qty
    );
    event Settled(
        uint256 indexed batchId,
        address indexed solver,
        uint256 price,
        uint256 dt,
        bool poolSells,
        uint256 reserveToken,
        uint256 reserveQuote
    );

    // ─── Errors ───────────────────────────────────────────────────────────────
    error AlreadySeeded();
    error NotSeeded();
    error ZeroSeed();
    error ZeroQty();
    error BatchNotOpen(uint256 batchId, uint256 open);
    error AlreadySettled(uint256 batchId);
    error TransferInFailed();
    error TransferOutFailed();

    constructor(address coin_, address stock_, address verifier_) {
        coin = IErc20Leg(coin_);
        stock = IErc20Leg(stock_);
        verifier = BatchClearingVerifier(verifier_);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Graduation — seed the pool ONCE from a cleared launch
    // ══════════════════════════════════════════════════════════════════════════
    /// @notice Seed the coin/stock pool ONCE (the graduation step). The caller must
    ///         have `approve`d this market for `coinSeed` coin + `stockSeed` stock
    ///         (the reserved coin allocation + the stock proceeds a launch batch
    ///         cleared into). Reserves/floors/fee are SET-ONCE here — no setter — so
    ///         the disclosed floors are as unchangeable as a constructor immutable.
    ///         After this, the pair trades per-block via `settle`, same `verifyClear`.
    function seedFromGraduation(
        uint256 coinSeed,
        uint256 stockSeed,
        uint256 floorToken_,
        uint256 floorQuote_,
        uint16 feeBps_
    ) external {
        if (seeded) revert AlreadySeeded();
        if (coinSeed == 0 || stockSeed == 0) revert ZeroSeed();
        seeded = true;
        if (!coin.transferFrom(msg.sender, address(this), coinSeed)) revert TransferInFailed();
        if (!stock.transferFrom(msg.sender, address(this), stockSeed)) revert TransferInFailed();
        reserveToken = coinSeed;
        reserveQuote = stockSeed;
        floorToken = floorToken_;
        floorQuote = floorQuote_;
        feeBps = feeBps_;
        emit Seeded(coinSeed, stockSeed, floorToken_, floorQuote_, feeBps_);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Order submission — plaintext, escrowed, into the open batch
    // ══════════════════════════════════════════════════════════════════════════
    /// @notice Submit a BUY: want up to `qty` coin at any price ≤ `limit`. Escrows
    ///         the MAX stock the order could ever pay — `ceil(limit·qty/WAD)` — so
    ///         settlement can always pull it. Unspent escrow is refunded at settle.
    function submitBuy(uint256 limit, uint256 qty) external returns (uint256 index) {
        if (!seeded) revert NotSeeded();
        if (qty == 0 || limit == 0) revert ZeroQty();
        uint256 escrow = _ceilDiv(limit * qty, WAD);
        if (!stock.transferFrom(msg.sender, address(this), escrow)) revert TransferInFailed();
        return _store(true, limit, qty, escrow);
    }

    /// @notice Submit a SELL: offer up to `qty` coin at any price ≥ `limit`. Escrows
    ///         the `qty` coin. Unfilled coin is refunded at settle.
    function submitSell(uint256 limit, uint256 qty) external returns (uint256 index) {
        if (!seeded) revert NotSeeded();
        if (qty == 0) revert ZeroQty();
        if (!coin.transferFrom(msg.sender, address(this), qty)) revert TransferInFailed();
        return _store(false, limit, qty, qty);
    }

    function _store(bool isBuy, uint256 limit, uint256 qty, uint256 escrow) private returns (uint256 index) {
        StoredOrder[] storage b = batchOrders[currentBatch];
        index = b.length;
        b.push(StoredOrder(isBuy, limit, qty, msg.sender, escrow));
        emit OrderSubmitted(currentBatch, index, msg.sender, isBuy, limit, qty);
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Settlement — permissionless; reuses verifyClear, then moves the tokens
    // ══════════════════════════════════════════════════════════════════════════
    /// @notice Anyone submits a candidate clear for the open batch. It is handed —
    ///         with the LIVE reserves and the STORED batch — to the verified
    ///         `verifyClear`; iff that accepts, tokens move at the single uniform
    ///         price `p` and reserves update. A rejected clear reverts (typed reason
    ///         propagates from the verifier); a batch settles at most once.
    ///
    /// ── Per-order base-unit rounding lives HERE (favor-the-pool) ──────────────
    /// The verifier asserts quote conservation at FULL precision (`p·Σbuy =
    /// p·Σsell + p·dt`), deferring the split into base-unit quote to this wrapper.
    /// We split per order:
    ///   • a BUYER PAYS  `ceil(p·fill/WAD)` stock   (rounded UP  — pays at least),
    ///   • a SELLER GETS `floor(p·fill/WAD)` stock  (rounded DOWN — gets at most).
    /// Every sub-wei residual therefore accrues to the POOL. The pool's stock
    /// reserve is credited the ACTUAL net it absorbs (`Σbuyerpay − Σsellerrecv`),
    /// which is `≥ floor(p·dt/WAD)` — the verifier's checked pool leg — so the
    /// settled reserves DOMINATE the model the verifier validated: `k′` and both
    /// floors hold at least as strongly as checked. Coin has no rounding (fills are
    /// base units); it conserves exactly via check 3 (`Σbuy − Σsell = dt`).
    function settle(uint256 batchId, BatchClearingVerifier.Clear calldata c) external {
        if (settled[batchId]) revert AlreadySettled(batchId);
        if (batchId != currentBatch) revert BatchNotOpen(batchId, currentBatch);

        StoredOrder[] storage b = batchOrders[batchId];
        uint256 n = b.length;

        // Build the verifier's Order[] from the stored batch (positional, O(n)).
        BatchClearingVerifier.Order[] memory ov = new BatchClearingVerifier.Order[](n);
        for (uint256 i = 0; i < n; i++) {
            StoredOrder storage s = b[i];
            ov[i] = BatchClearingVerifier.Order(s.isBuy, s.limit, s.qty, s.who);
        }
        BatchClearingVerifier.Reserves memory r =
            BatchClearingVerifier.Reserves(reserveToken, reserveQuote, floorToken, floorQuote, feeBps);

        // REUSE THE VERIFIED CORE. Reverts (typed) on any failed check ⇒ no settle.
        verifier.verifyClear(ov, r, c);

        // Passed. Move tokens at the uniform price; refund unspent escrow.
        uint256 sumBuyerPay; // Σ ceil(p·fill/WAD) over filled BUYs
        uint256 sumSellerRecv; // Σ floor(p·fill/WAD) over filled SELLs
        for (uint256 i = 0; i < n; i++) {
            StoredOrder storage s = b[i];
            uint256 fill = c.fills[i];
            if (s.isBuy) {
                uint256 pay = fill == 0 ? 0 : _ceilDiv(c.p * fill, WAD); // favor-pool: round UP
                sumBuyerPay += pay;
                if (fill > 0) _out(coin, s.who, fill); // buyer receives coin
                uint256 refund = s.escrow - pay; // unspent stock back
                if (refund > 0) _out(stock, s.who, refund);
            } else {
                uint256 recv = fill == 0 ? 0 : (c.p * fill) / WAD; // favor-pool: round DOWN
                sumSellerRecv += recv;
                if (recv > 0) _out(stock, s.who, recv); // seller receives stock
                uint256 refund = s.escrow - fill; // unfilled coin back
                if (refund > 0) _out(coin, s.who, refund);
            }
        }

        // Pool leg. Coin: exact (check 3). Quote: the ACTUAL net the pool absorbs/pays
        // — ≥/≤ the verifier's floored `p·dt/WAD`, so reserves dominate the model.
        if (c.poolSells) {
            reserveToken -= c.dt; // pool sold dt coin into the batch
            reserveQuote += (sumBuyerPay - sumSellerRecv); // pool took the net stock (+ residual)
        } else {
            reserveToken += c.dt; // pool absorbed dt coin
            reserveQuote -= (sumSellerRecv - sumBuyerPay); // pool paid the net stock
        }

        settled[batchId] = true;
        currentBatch = batchId + 1;
        emit Settled(batchId, msg.sender, c.p, c.dt, c.poolSells, reserveToken, reserveQuote);
    }

    // ─── Views ──────────────────────────────────────────────────────────────────
    function batchLength(uint256 batchId) external view returns (uint256) {
        return batchOrders[batchId].length;
    }

    /// The open batch as the verifier's `Order[]` — what a solver reads to clear.
    function getBatchOrders(uint256 batchId) external view returns (BatchClearingVerifier.Order[] memory ov) {
        StoredOrder[] storage b = batchOrders[batchId];
        ov = new BatchClearingVerifier.Order[](b.length);
        for (uint256 i = 0; i < b.length; i++) {
            ov[i] = BatchClearingVerifier.Order(b[i].isBuy, b[i].limit, b[i].qty, b[i].who);
        }
    }

    function reserves() external view returns (uint256 tokenR, uint256 quoteR) {
        return (reserveToken, reserveQuote);
    }

    // ─── Internal ─────────────────────────────────────────────────────────────
    function _ceilDiv(uint256 a, uint256 b) private pure returns (uint256) {
        if (a == 0) return 0;
        return (a - 1) / b + 1;
    }

    function _out(IErc20Leg t, address to, uint256 amount) private {
        if (!t.transfer(to, amount)) revert TransferOutFailed();
    }
}
