// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {DreggLaunchToken} from "./DreggLaunchToken.sol";

/// @title DreggSolventPool
/// @notice The PROVABLY-SOLVENT liquid market a fair launch GRADUATES into — the
///         EVM realization of DrEX **rung 6**, `Market/Liquidity.lean`'s
///         never-insolvent pool (`pool_solvent_forever`), and the differentiator
///         vs a pump.fun bonding curve (drainable) or a Raydium pool (no solvency
///         theorem). Seeded once from a cleared raise (a disclosed fraction of the
///         proceeds as the QUOTE reserve + a reserved token allocation as the TOKEN
///         reserve), it is then a standing constant-product (`x·y=k`) trading venue.
///
/// ## The solvency guarantee (the tooth)
/// Every swap enforces a DISCLOSED per-reserve FLOOR: a trade whose output would
/// push a reserve below its floor REVERTS (`PoolFloorBreached`). This is the
/// on-chain realization of `Market/Liquidity.lean`'s `PoolFillValid` discipline
/// (`filledOut ≤ reserve`, generalized to `reserveOut - output ≥ floor`): the pool
/// can only ever disburse down to its floor, so it is NEVER insolvent — no trade,
/// no sequence of trades, can drain it below the floor.
///
/// The tie is `metatheory/Market/GraduationPool.lean`
/// (`graduated_pool_solvent_forever`): the floor guard `require(reserveOut - out ≥
/// floor)` is a `PoolFillValidFloor` discipline, which — floor being nonnegative —
/// REFINES rung-6's `PoolFillValid`, so the deployed pool realizes
/// `pool_solvent_forever`. `floor = 0` is the exact rung-6 never-negative case; the
/// launchpad graduates with a positive disclosed floor (strictly stronger).
///
/// ## Honest scope
/// - The SOLVENCY floor is PROVED off-chain (rung 6) + on-chain-enforced here
///   (`PoolFloorBreached`, tested both polarities). This is the load-bearing claim.
/// - The `x·y=k` constant-product PRICING is BUILT here (a swap keeps `x·y`
///   non-decreasing under the fee, `ConstantProductViolated` guards it) — the
///   pricing policy ABOVE the solvency floor, exactly as `Market/Liquidity.lean`
///   frames it (the floor is the guarantee; the curve is the policy).
///
/// Quote currency is native ETH (Robinhood Chain / Base-Sepolia gas token).
contract DreggSolventPool {
    DreggLaunchToken public immutable token;
    /// The launchpad that graduated the launch — the only address allowed to seed.
    address public immutable graduation;
    /// Provenance: which launch this pool graduated from.
    uint256 public immutable launchId;

    /// The live reserves (tracked internally, not via `balanceOf`, so a token
    /// donation cannot move the price or the solvency accounting).
    uint256 public reserveQuote; // wei
    uint256 public reserveToken; // token base units

    /// The DISCLOSED reserve floors — the minimum each reserve may never drop
    /// below. Set at graduation to a disclosed fraction of the seed. `floor = 0`
    /// is the exact rung-6 never-negative case.
    uint256 public immutable floorQuote;
    uint256 public immutable floorToken;

    /// The swap fee in basis points (e.g. 30 = 0.30%). The fee makes `x·y`
    /// strictly grow — the constant-product invariant is non-decreasing.
    uint16 public immutable feeBps;

    bool public initialized;

    // ─── Events ───────────────────────────────────────────────────────────────
    event Initialized(uint256 reserveQuote, uint256 reserveToken, uint256 floorQuote, uint256 floorToken);
    event Bought(
        address indexed buyer, uint256 quoteIn, uint256 tokenOut, uint256 reserveQuote, uint256 reserveToken
    );
    event Sold(
        address indexed seller, uint256 tokenIn, uint256 quoteOut, uint256 reserveQuote, uint256 reserveToken
    );

    // ─── Errors ───────────────────────────────────────────────────────────────
    error NotGraduation();
    error AlreadyInitialized();
    error NotInitialized();
    error ZeroInput();
    error SeedTokensMissing(uint256 have, uint256 need);
    /// THE SOLVENCY TOOTH: a swap whose output would push a reserve below its
    /// disclosed floor — refused (rung-6 `pool_solvent_forever`, on-chain).
    error PoolFloorBreached(uint256 reserveAfter, uint256 floor);
    /// The constant-product invariant `x·y` must be non-decreasing under the fee.
    error ConstantProductViolated();
    error InsufficientOutput(uint256 out, uint256 min);
    error TransferFromFailed();
    error TransferFailed();

    constructor(
        address token_,
        uint256 launchId_,
        uint256 floorQuote_,
        uint256 floorToken_,
        uint16 feeBps_
    ) {
        token = DreggLaunchToken(token_);
        graduation = msg.sender;
        launchId = launchId_;
        floorQuote = floorQuote_;
        floorToken = floorToken_;
        feeBps = feeBps_;
    }

    /// @notice Seed the pool ONCE (called by the graduation). ETH arrives as
    ///         `msg.value` (the quote reserve); `tokenSeed` tokens must already
    ///         have been transferred in (the token reserve). Only the graduation
    ///         can seed, and only once.
    function initialize(uint256 tokenSeed) external payable {
        if (msg.sender != graduation) revert NotGraduation();
        if (initialized) revert AlreadyInitialized();
        if (msg.value == 0 || tokenSeed == 0) revert ZeroInput();
        uint256 bal = token.balanceOf(address(this));
        if (bal < tokenSeed) revert SeedTokensMissing(bal, tokenSeed);
        initialized = true;
        reserveQuote = msg.value;
        reserveToken = tokenSeed;
        emit Initialized(reserveQuote, reserveToken, floorQuote, floorToken);
    }

    // ─── Trading (constant product `x·y=k`, solvency-floored) ───────────────────

    /// @notice Buy tokens with ETH. Output priced by the constant-product curve
    ///         (`out = reserveToken·quoteInNet / (reserveQuote + quoteInNet)`); the
    ///         resulting token reserve MUST stay at or above `floorToken`, else the
    ///         trade reverts (`PoolFloorBreached`) — the pool cannot be drained.
    function buy(uint256 minTokenOut) external payable returns (uint256 tokenOut) {
        if (!initialized) revert NotInitialized();
        if (msg.value == 0) revert ZeroInput();
        uint256 kBefore = reserveQuote * reserveToken;

        uint256 quoteInNet = (msg.value * (10000 - feeBps)) / 10000;
        tokenOut = (reserveToken * quoteInNet) / (reserveQuote + quoteInNet);
        if (tokenOut < minTokenOut) revert InsufficientOutput(tokenOut, minTokenOut);

        uint256 reserveTokenAfter = reserveToken - tokenOut;
        // THE SOLVENCY TOOTH — never below the disclosed floor (rung-6).
        if (reserveTokenAfter < floorToken) revert PoolFloorBreached(reserveTokenAfter, floorToken);

        reserveQuote += msg.value; // the WHOLE input (incl. fee) stays in the pool
        reserveToken = reserveTokenAfter;
        // `x·y` non-decreasing (the fee grows k) — the constant-product policy.
        if (reserveQuote * reserveToken < kBefore) revert ConstantProductViolated();

        _sendToken(msg.sender, tokenOut);
        emit Bought(msg.sender, msg.value, tokenOut, reserveQuote, reserveToken);
    }

    /// @notice Sell `tokenIn` tokens for ETH (caller must `approve` this pool).
    ///         Symmetric to `buy`: the resulting quote reserve MUST stay at or
    ///         above `floorQuote`, else the trade reverts (`PoolFloorBreached`).
    function sell(uint256 tokenIn, uint256 minQuoteOut) external returns (uint256 quoteOut) {
        if (!initialized) revert NotInitialized();
        if (tokenIn == 0) revert ZeroInput();
        if (!token.transferFrom(msg.sender, address(this), tokenIn)) revert TransferFromFailed();
        uint256 kBefore = reserveQuote * reserveToken;

        uint256 tokenInNet = (tokenIn * (10000 - feeBps)) / 10000;
        quoteOut = (reserveQuote * tokenInNet) / (reserveToken + tokenInNet);
        if (quoteOut < minQuoteOut) revert InsufficientOutput(quoteOut, minQuoteOut);

        uint256 reserveQuoteAfter = reserveQuote - quoteOut;
        // THE SOLVENCY TOOTH — never below the disclosed floor (rung-6).
        if (reserveQuoteAfter < floorQuote) revert PoolFloorBreached(reserveQuoteAfter, floorQuote);

        reserveToken += tokenIn; // the WHOLE input (incl. fee) stays in the pool
        reserveQuote = reserveQuoteAfter;
        if (reserveQuote * reserveToken < kBefore) revert ConstantProductViolated();

        _sendEth(msg.sender, quoteOut);
        emit Sold(msg.sender, tokenIn, quoteOut, reserveQuote, reserveToken);
    }

    // ─── Views ──────────────────────────────────────────────────────────────────

    /// @notice The spot price: wei of quote per WHOLE token (`reserveQuote·1e18 /
    ///         reserveToken`). The honest on-chain price — read from the reserves,
    ///         not a market-cap fiction.
    function spotPriceWeiPerToken() external view returns (uint256) {
        if (reserveToken == 0) return 0;
        return (reserveQuote * 1e18) / reserveToken;
    }

    /// @notice A quote for buying with `quoteIn` wei (the token output, no state
    ///         change) — the same math `buy` uses, for a UI to preview.
    function quoteBuy(uint256 quoteIn) external view returns (uint256 tokenOut) {
        if (!initialized || quoteIn == 0) return 0;
        uint256 quoteInNet = (quoteIn * (10000 - feeBps)) / 10000;
        tokenOut = (reserveToken * quoteInNet) / (reserveQuote + quoteInNet);
    }

    function reserves() external view returns (uint256 quote, uint256 tokenR) {
        return (reserveQuote, reserveToken);
    }

    function floors() external view returns (uint256 quote, uint256 tokenR) {
        return (floorQuote, floorToken);
    }

    // ─── Internal ─────────────────────────────────────────────────────────────
    function _sendToken(address to, uint256 amount) private {
        if (!token.transfer(to, amount)) revert TransferFailed();
    }

    function _sendEth(address to, uint256 amount) private {
        (bool ok,) = payable(to).call{value: amount}("");
        if (!ok) revert TransferFailed();
    }
}
