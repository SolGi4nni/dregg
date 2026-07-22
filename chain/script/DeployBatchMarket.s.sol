// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Script.sol";
import {BatchClearingVerifier} from "../contracts/launchpad/BatchClearingVerifier.sol";
import {BatchClearedMarket} from "../contracts/launchpad/BatchClearedMarket.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {MockStockToken} from "../contracts/launchpad/MockStockToken.sol";

/// @title DeployBatchMarket
/// @notice Deploys the RUNNABLE coin/stock uniform-price batch-cleared market
///         (Rung 3 of `docs/deos/FAIR-BATCH-MARKET-DESIGN.md`) — the tangible,
///         clickable demo behind the Clark / Robinhood-Chain launchpad push. It
///         deploys, in one broadcast:
///           1. `BatchClearingVerifier` — the VERIFIED clearing predicate (pure).
///           2. `DreggLaunchToken` ($DEMO)  — the launched coin, the TOKEN leg.
///           3. `MockStockToken` (mNVDA)     — the stock, the QUOTE leg (test mint).
///           4. `BatchClearedMarket`         — the settlement wrapper around #1.
///         then SEEDS the coin/mNVDA pool once via `seedFromGraduation` (the
///         graduation step), so the pair trades per-batch immediately.
///
///         Chain-agnostic rung-1 standard EVM. Primary target Base-Sepolia
///         (chainId 84532); Robinhood Chain testnet (Arbitrum-Orbit L2, chainId
///         46630, ETH gas) is the drop-in alternative — same bytecode, same
///         broadcast, different `--rpc-url`.
///
/// ============================ EMBER: ONE-COMMAND BROADCAST ==================
///
///   # 0. one-time: a funded deployer key + the RPC env.
///   export DEPLOYER_PRIVATE_KEY=0x<funded key>            # EMBER input
///   # Base-Sepolia (primary):
///   export BASE_SEPOLIA_RPC_URL=https://sepolia.base.org
///   # or Robinhood Chain testnet (drop-in alternative):
///   export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com
///
///   # 1. THE BROADCAST (the ember/outward step — real txs). Base-Sepolia:
///   forge script script/DeployBatchMarket.s.sol:DeployBatchMarket \
///       --rpc-url base_sepolia --broadcast -vvv
///
///   #    Robinhood Chain instead:
///   forge script script/DeployBatchMarket.s.sol:DeployBatchMarket \
///       --rpc-url robinhood_testnet --broadcast -vvv
///
///   #    (Blockscout verify on Robinhood Chain, optional:)
///   #      ... --verify --verifier blockscout \
///   #          --verifier-url https://explorer.testnet.chain.robinhood.com/api/
///
/// Dry-run first (no key/tx — simulates the deploy AND a full batch: seed →
/// 6-order book → permissionless solver clear → settle → asserts the receipt):
///   forge script script/DeployBatchMarket.s.sol:DeployBatchMarket
///
/// HONEST NOTE: the broadcast + the funded key are the EMBER/outward step. This
/// script is the dry-run-verified plumbing that makes "point at Base-Sepolia /
/// Robinhood Chain" one command away. Nothing here broadcasts on its own. Orders
/// are PLAINTEXT (front-runnable at the mempool until the fhegg encryption rung);
/// the deployed proof path is FRI-floored, not "trustless" — see rhlp-web/README.md.
/// ===========================================================================
contract DeployBatchMarket is Script {
    /// The well-known anvil dev key — used ONLY so a keyless dry-run can simulate.
    uint256 constant ANVIL_DEV_KEY = 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80;

    uint256 internal constant WAD = 1e18;

    // ── demo economics (the graduation seed; disclosed, set-once) ──────────────
    uint256 constant CAP = 10_000e18; // $DEMO hard cap
    uint256 constant SEED_COIN = 1000e18; // Rt — coin reserve
    uint256 constant SEED_STOCK = 2000e18; // Rq — mNVDA reserve (⇒ ~2.0 mNVDA/coin spot)
    uint256 constant FLOOR = 1e18; // both solvency floors
    uint16 constant FEE = 30; // 0.30% LP fee (bps; reserved)

    function run() external {
        uint256 deployerPk = vm.envOr("DEPLOYER_PRIVATE_KEY", ANVIL_DEV_KEY);
        address deployer = vm.addr(deployerPk);

        console.log("== dregg batch-market deploy (Base-Sepolia / Robinhood Chain) ==");
        console.log("chainId :", block.chainid);
        console.log("deployer:", deployer);

        vm.startBroadcast(deployerPk);

        // 1. the VERIFIED clearing predicate (pure, reused — never reimplemented)
        BatchClearingVerifier verifier = new BatchClearingVerifier();

        // 2. the launched coin ($DEMO). The deployer is the sole minter and mints
        //    the full disclosed cap once (the "no hidden supply" door).
        DreggLaunchToken coin = new DreggLaunchToken("Dregg Demo Coin", "DEMO", CAP, deployer);
        coin.mint(deployer, CAP);

        // 3. the stock leg — a mock tokenized NVDA (TEST mint, see MockStockToken).
        MockStockToken stock = new MockStockToken("Mock NVDA", "mNVDA");

        // 4. the settlement market over the verified predicate.
        BatchClearedMarket market = new BatchClearedMarket(address(coin), address(stock), address(verifier));

        // ── Graduation: seed the coin/mNVDA pool ONCE (set-once floors/fee) ──────
        stock.mint(deployer, SEED_STOCK);
        coin.approve(address(market), SEED_COIN);
        stock.approve(address(market), SEED_STOCK);
        market.seedFromGraduation(SEED_COIN, SEED_STOCK, FLOOR, FLOOR, FEE);

        vm.stopBroadcast();

        console.log("-----------------------------------------------------------");
        console.log("BatchClearingVerifier :", address(verifier));
        console.log("DreggLaunchToken DEMO :", address(coin));
        console.log("MockStockToken  mNVDA :", address(stock));
        console.log("BatchClearedMarket    :", address(market));
        console.log("  seeded Rt (coin)    :", SEED_COIN);
        console.log("  seeded Rq (mNVDA)   :", SEED_STOCK);
        console.log("  spot mNVDA/coin     : ~2.0 (Rq/Rt)");
        console.log("-----------------------------------------------------------");
        console.log("Wire the web app:  RHLP_MARKET_ADDRESS=%s  (rhlp-web/server.mjs)", address(market));

        // ---- the DRY-RUN demo: a full batch, simulation-only ----
        if (vm.envOr("RHLP_MARKET_DEMO", true)) {
            _demoBatch(market, coin, stock, deployer);
        } else {
            console.log("demo batch SKIPPED (RHLP_MARKET_DEMO=false).");
            console.log("Anyone can submitBuy/submitSell then settle a batch on this deploy.");
        }
    }

    // ══════════════════════════════════════════════════════════════════════════
    // DRY-RUN demo: the canonical 6-order book → permissionless clear → settle.
    // The order book + clear are the exact fixture BatchClearedMarket.t.sol /
    // clearing_check3.py validate: Rt=1000e18, Rq=2000e18, p*=2.2, dt pinned.
    // ══════════════════════════════════════════════════════════════════════════
    function _demoBatch(BatchClearedMarket market, DreggLaunchToken coin, MockStockToken stock, address deployer)
        internal
    {
        console.log(">> DEMO BATCH (dry-run simulation) ---------------------------");

        // canonical clear: p*=2.2, dt pinned, marginal SELL 2.20 fill = XMARG.
        // BUY escrows ceil(limit*qty/WAD) stock; deployer funds the actors' escrow.
        _fundBuy(market, stock, vm.addr(0xB0), 230e18, 230e16, 100e18); // BUY 2.30 100
        _fundSell(market, coin, deployer, vm.addr(0xB3), 195e16, 40e18); // SELL 1.95 40
        _fundSell(market, coin, deployer, vm.addr(0xB4), 220e16, 30e18); // SELL 2.20 30 (marginal)
        console.log("  batch collected orders:", market.batchLength(0));

        // a permissionless solver submits the clear; verifyClear gates it.
        uint256[] memory f = new uint256[](3);
        f[0] = 100e18; // BUY 2.30 fully filled
        f[1] = 40e18; // SELL 1.95 fully filled
        f[2] = 13462589245592315447; // SELL 2.20 marginal fill (XMARG)

        vm.prank(vm.addr(0x5011E7)); // permissionless solver
        market.settle(0, BatchClearingVerifier.Clear(22e17, f, 46537410754407684553, true));

        _printReceipt(market, coin, stock);
    }

    function _printReceipt(BatchClearedMarket market, DreggLaunchToken coin, MockStockToken stock) internal view {
        (uint256 rt1, uint256 rq1) = market.reserves();
        console.log("  cleared at uniform p  : 2.2 mNVDA/coin");
        console.log("  pool sold dt coin     :", uint256(46537410754407684553));
        console.log("  Rt' (coin reserve)    :", rt1);
        console.log("  Rq' (mNVDA reserve)   :", rq1);
        require(rt1 * rq1 >= SEED_COIN * SEED_STOCK, "demo: k' >= k (LVR captured)");
        require(market.settled(0), "demo: batch settled");
        console.log("  k' >= k (LVR captured): true");
        console.log("  A0 coin bought        :", coin.balanceOf(vm.addr(0xB0)));
        console.log("  A3 mNVDA received     :", stock.balanceOf(vm.addr(0xB3)));
        console.log(">> DEMO BATCH cleared at ONE uniform price. No front-run; LPs kept the LVR.");
    }

    function _fundBuy(
        BatchClearedMarket market,
        MockStockToken stock,
        address who,
        uint256 escrow,
        uint256 limit,
        uint256 qty
    ) internal {
        stock.mint(who, escrow);
        vm.startPrank(who);
        stock.approve(address(market), escrow);
        market.submitBuy(limit, qty);
        vm.stopPrank();
    }

    function _fundSell(
        BatchClearedMarket market,
        DreggLaunchToken coin,
        address deployer,
        address who,
        uint256 limit,
        uint256 qty
    ) internal {
        vm.prank(deployer);
        coin.transfer(who, qty);
        vm.startPrank(who);
        coin.approve(address(market), qty);
        market.submitSell(limit, qty);
        vm.stopPrank();
    }
}
