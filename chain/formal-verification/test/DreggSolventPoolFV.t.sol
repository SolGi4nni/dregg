// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {DreggLaunchToken} from "contracts/launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "contracts/launchpad/DreggSolventPool.sol";

/// @title DreggSolventPool — SYMBOLIC formal verification (Halmos)
/// @notice Proves the NEVER-DRAINABLE (solvency-floor) invariant against the REAL
///         compiled `DreggSolventPool` bytecode, over ALL trade inputs (symbolic),
///         for a bounded call sequence.
///
/// LEAN TIE:
///   * `pool_solvent_forever` (metatheory/Market/Liquidity.lean:145) — under ANY
///     valid schedule the reserve is NEVER driven insolvent.
///   * `graduated_pool_solvent_forever` (metatheory/Market/GraduationPool.lean:116)
///     — the on-chain floor guard is a `PoolFillValidFloor` discipline that REFINES
///     rung-6's `PoolFillValid` (`poolFillValidFloor_refines`, GraduationPool.lean:66).
///   The EVM twin proved here: NO trade, and no sequence of trades, by ANYONE, can
///   push a reserve below its disclosed floor.
///
/// WHY HALMOS (not solc CHC): the floor guard reverts with a custom error
/// (`revert PoolFloorBreached(...)`), which solc's CHC engine models as fall-through
/// (spurious CEX). Halmos runs the bytecode, so the revert is a real REVERT opcode.
///
/// BOUND: reserves/floors/fee symbolic but bounded to ~1e30 (well above any realistic
/// launch, well below the uint256 overflow band of the `x*y` product) to keep the
/// nonlinear constant-product arithmetic tractable for the SMT solver. Trade amounts
/// fully symbolic. Call-depth bounded (single call + 2-step sequence). This is a
/// symbolic-bounded proof — see README §The honest gap.
contract DreggSolventPoolFV is Test {
    uint256 constant BOUND = 1e30; // reserve/amount ceiling (see BOUND note above)

    // Build an initialized, above-floor pool with symbolic seed/floors/fee.
    function _init(
        uint256 quoteSeed,
        uint256 tokenSeed,
        uint256 floorQuote,
        uint256 floorToken,
        uint16 feeBps
    ) internal returns (DreggSolventPool pool, DreggLaunchToken token) {
        vm.assume(feeBps < 10000);
        vm.assume(quoteSeed != 0 && quoteSeed < BOUND);
        vm.assume(tokenSeed != 0 && tokenSeed < BOUND);
        // Graduation seeds AT or ABOVE the disclosed floor (the launchpad discipline).
        vm.assume(floorToken <= tokenSeed);
        vm.assume(floorQuote <= quoteSeed);

        token = new DreggLaunchToken("N", "S", BOUND, address(this));
        token.mint(address(this), BOUND - 1); // this contract holds all tokens
        pool = new DreggSolventPool(address(token), 1, floorQuote, floorToken, feeBps);
        token.transfer(address(pool), tokenSeed);
        vm.deal(address(this), quoteSeed);
        pool.initialize{value: quoteSeed}(tokenSeed);
    }

    // ── INVARIANT — BUY never drains the TOKEN reserve below its floor ────────────
    function check_buy_neverBelowFloor(
        uint256 quoteSeed, uint256 tokenSeed, uint256 floorQuote, uint256 floorToken, uint16 feeBps,
        address buyer, uint256 quoteIn, uint256 minOut
    ) public {
        (DreggSolventPool pool,) = _init(quoteSeed, tokenSeed, floorQuote, floorToken, feeBps);
        vm.assume(quoteIn < BOUND);
        vm.assume(buyer != address(pool) && buyer != address(this));
        vm.deal(buyer, quoteIn);

        vm.prank(buyer);
        try pool.buy{value: quoteIn}(minOut) {
            (, uint256 rTok) = pool.reserves();
            (, uint256 flTok) = pool.floors();
            assert(rTok >= flTok); // THE SOLVENCY TOOTH, proven
        } catch {
            // reverted ⇒ reserves untouched, still above floor
            (, uint256 rTok) = pool.reserves();
            (, uint256 flTok) = pool.floors();
            assert(rTok >= flTok);
        }
    }

    // ── INVARIANT — SELL never drains the QUOTE reserve below its floor ───────────
    function check_sell_neverBelowFloor(
        uint256 quoteSeed, uint256 tokenSeed, uint256 floorQuote, uint256 floorToken, uint16 feeBps,
        address seller, uint256 tokenIn, uint256 minOut
    ) public {
        (DreggSolventPool pool, DreggLaunchToken token) =
            _init(quoteSeed, tokenSeed, floorQuote, floorToken, feeBps);
        vm.assume(tokenIn != 0 && tokenIn < BOUND);
        vm.assume(seller != address(pool) && seller != address(this));

        // Fund the seller with tokens and let the pool pull them.
        token.transfer(seller, tokenIn);
        vm.prank(seller);
        token.approve(address(pool), tokenIn);

        vm.prank(seller);
        try pool.sell(tokenIn, minOut) {
            (uint256 rQuote,) = pool.reserves();
            (uint256 flQuote,) = pool.floors();
            assert(rQuote >= flQuote); // THE SOLVENCY TOOTH, proven
        } catch {
            (uint256 rQuote,) = pool.reserves();
            (uint256 flQuote,) = pool.floors();
            assert(rQuote >= flQuote);
        }
    }

    // ── INVARIANT — a BUY→SELL sequence keeps BOTH reserves above their floors ────
    // No two-step drain: no combination of a buy then a sell breaches either floor.
    function check_buyThenSell_neverBelowFloor(
        uint256 quoteSeed, uint256 tokenSeed, uint256 floorQuote, uint256 floorToken, uint16 feeBps,
        address actor, uint256 quoteIn, uint256 tokenIn
    ) public {
        (DreggSolventPool pool, DreggLaunchToken token) =
            _init(quoteSeed, tokenSeed, floorQuote, floorToken, feeBps);
        vm.assume(quoteIn < BOUND && tokenIn < BOUND);
        vm.assume(actor != address(pool) && actor != address(this));

        vm.deal(actor, quoteIn);
        vm.prank(actor);
        try pool.buy{value: quoteIn}(0) {} catch {}
        _assertAboveFloors(pool);

        token.transfer(actor, tokenIn);
        vm.prank(actor);
        token.approve(address(pool), tokenIn);
        vm.prank(actor);
        try pool.sell(tokenIn, 0) {} catch {}
        _assertAboveFloors(pool);
    }

    function _assertAboveFloors(DreggSolventPool pool) internal view {
        (uint256 rQuote, uint256 rTok) = pool.reserves();
        (uint256 flQuote, uint256 flTok) = pool.floors();
        assert(rQuote >= flQuote);
        assert(rTok >= flTok);
    }
}
