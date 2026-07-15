// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Script.sol";
import {DreggLaunchpad} from "../contracts/launchpad/DreggLaunchpad.sol";
import {DreggLaunchToken} from "../contracts/launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "../contracts/launchpad/DreggSolventPool.sol";
import {ILaunchEligibility} from "../contracts/launchpad/ILaunchEligibility.sol";
import {IClearingAttestor} from "../contracts/launchpad/IClearingAttestor.sol";
import {IDeployerGate} from "../contracts/launchpad/IDeployerGate.sol";

/// @title DeployLaunchpad
/// @notice Deploys the provably-fair `DreggLaunchpad` (the launch flow of
///         `docs/deos/DREGG-LAUNCHPAD-DESIGN.md` §2) to Robinhood Chain
///         (Arbitrum-Orbit EVM L2, chainId 46630) or Base-Sepolia (84532), then
///         DRY-RUN demonstrates a full fair launch end-to-end
///         (register → sealed commit → reveal → uniform-price clear → settle).
///
///         The broadcast deploys ONE contract — the launchpad — and it is ready
///         for real launches immediately. The demo launch is run as a LOCAL
///         SIMULATION (it needs the commit/reveal windows to elapse, which
///         `vm.warp` does only in-simulation), so it proves the deployed flow
///         without sending its lifecycle txs on a live chain.
///
/// ============================ EMBER: ONE-COMMAND BROADCAST ==================
///
///   # 0. one-time: a funded deployer key + the RPC env. Robinhood Chain is a
///   #    permissionless Orbit L2 (ETH gas); our deployer key is funded.
///   export DEPLOYER_PRIVATE_KEY=0x<funded robinhood-chain key>   # EMBER input
///   export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com
///
///   # 1. THE ROBINHOOD-CHAIN BROADCAST (the ember/outward step — a real tx):
///   forge script script/DeployLaunchpad.s.sol:DeployLaunchpad \
///       --rpc-url robinhood_testnet --broadcast -vvv
///
///   #    (Blockscout verify, optional:)
///   #      ... --verify --verifier blockscout \
///   #          --verifier-url https://explorer.testnet.chain.robinhood.com/api/
///
///   # Base-Sepolia instead: --rpc-url base_sepolia --broadcast --verify
///
/// Dry-run first (no key/tx — simulates the deploy AND the full demo launch,
/// asserts it clears at the uniform price, prints sim addresses/gas):
///   forge script script/DeployLaunchpad.s.sol:DeployLaunchpad
///
/// HONEST NOTE: the broadcast + the funded key are the EMBER/outward step. This
/// script is the dry-run-verified plumbing that makes "point at Robinhood Chain"
/// one command away. Nothing here broadcasts on its own. Post-deploy, ember (or
/// anyone — registration is permissionless) calls `registerLaunch` to run a real
/// launch; the commit/reveal windows then elapse in real time.
/// ===========================================================================
contract DeployLaunchpad is Script {
    /// The well-known anvil dev key — used ONLY so a keyless dry-run can simulate.
    uint256 constant ANVIL_DEV_KEY =
        0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80;

    uint256 constant G = 1e9; // gwei price unit for the demo

    function run() external {
        uint256 deployerPk = vm.envOr("DEPLOYER_PRIVATE_KEY", ANVIL_DEV_KEY);
        address deployer = vm.addr(deployerPk);

        console.log("== dregg launchpad deploy (Robinhood Chain / Base-Sepolia) ==");
        console.log("chainId :", block.chainid);
        console.log("deployer:", deployer);

        // ---- the broadcast: deploy the launchpad (the one live contract) ----
        vm.startBroadcast(deployerPk);
        // The deployer gate is PINNED AT CONSTRUCTION and immutable. `address(0)`
        // = permissionless deploy (this demo's posture). To run a deployer-gated
        // launchpad, deploy a `DreggDeployerGate` first (choosing its arms: bond /
        // skeptical-Opus interview / cleared audit) and pass it here — the choice
        // is a property of the deployment, not a switch an operator can flip later.
        DreggLaunchpad pad = new DreggLaunchpad(IDeployerGate(vm.envOr("DREGG_DEPLOYER_GATE", address(0))));
        vm.stopBroadcast();

        console.log("-----------------------------------------------------------");
        console.log("DreggLaunchpad :", address(pad));
        console.log("-----------------------------------------------------------");

        // ---- the DRY-RUN demo: a full fair launch, simulation-only ----
        if (vm.envOr("DREGG_LAUNCHPAD_DEMO", true)) {
            _demoLaunch(pad);
        } else {
            console.log("demo launch SKIPPED (DREGG_LAUNCHPAD_DEMO=false).");
            console.log("Call registerLaunch to run a real launch on this deploy.");
        }
    }

    /// The full launch lifecycle against the deployed contract, as a local
    /// simulation (warps the commit/reveal windows). Asserts the uniform clearing.
    function _demoLaunch(DreggLaunchpad pad) internal {
        console.log(">> DEMO LAUNCH (dry-run simulation) --------------------------");

        address creator = vm.addr(0xC0FFEE);
        address alice = vm.addr(0xA11CE);
        address bob = vm.addr(0xB0B);
        address carol = vm.addr(0xCA401);
        address dave = vm.addr(0xDA5E);
        vm.deal(creator, 10 ether);
        vm.deal(alice, 10 ether);
        vm.deal(bob, 10 ether);
        vm.deal(carol, 10 ether);
        vm.deal(dave, 10 ether);

        // (a) register: disclosed schedule, supply closes (1000 sale + 100 creator
        //     + 100 pool = 1200 total). No hidden supply is expressible. 50% of the
        //     raise proceeds graduate into the solvent pool (graduationBps = 5000).
        DreggLaunchpad.Schedule memory s = DreggLaunchpad.Schedule({
            totalSupply: 1200,
            saleSupply: 1000,
            creatorAllocation: 100,
            poolAllocation: 100,
            graduationBps: 5000,
            creatorLockUntil: uint64(block.timestamp) + 30 days,
            reservePrice: 1 * G
        });
        vm.prank(creator);
        uint256 id =
            pad.registerLaunch(
            "DreggDemo", "DDEMO", s, 100, 100, ILaunchEligibility(address(0)), IClearingAttestor(address(0)), ""
        );
        console.log("  launch id            :", id);
        console.log("  launch token         :", pad.tokenOf(id));
        console.log("  schedule disclosed OK :", pad.checkSchedule(id, s));

        // (b) sealed commits — 5,4,3,2 gwei/token, 400 each.
        _commit(pad, id, alice, 5 * G, 400, keccak256("a"));
        _commit(pad, id, bob, 4 * G, 400, keccak256("b"));
        _commit(pad, id, carol, 3 * G, 400, keccak256("c"));
        _commit(pad, id, dave, 2 * G, 400, keccak256("d"));
        console.log("  sealed commits        : 4 (no bid observable)");

        // reveal window
        vm.warp(block.timestamp + 100);
        vm.prank(alice);
        pad.revealBid(id, 5 * G, 400, keccak256("a"));
        vm.prank(bob);
        pad.revealBid(id, 4 * G, 400, keccak256("b"));
        vm.prank(carol);
        pad.revealBid(id, 3 * G, 400, keccak256("c"));
        vm.prank(dave);
        pad.revealBid(id, 2 * G, 400, keccak256("d"));
        console.log("  reveals               :", pad.revealedCount(id));

        // (c) uniform-price clearing (sorted desc: alice,bob,carol,dave).
        vm.warp(block.timestamp + 100);
        uint256[] memory order = new uint256[](4);
        order[0] = 0;
        order[1] = 1;
        order[2] = 2;
        order[3] = 3;
        pad.finalizeClearing(id, order, "");
        console.log("  uniform clearing price:", pad.clearingPriceOf(id));
        console.log("  tokens sold           :", pad.soldQtyOf(id));
        require(pad.clearingPriceOf(id) == 3 * G, "demo: uniform price should be 3 gwei");
        require(pad.soldQtyOf(id) == 1000, "demo: full saleSupply should clear");

        // (d) settle — every winner pays the SAME price; refunds returned.
        pad.settleBid(id, alice);
        pad.settleBid(id, bob);
        pad.settleBid(id, carol);
        pad.settleBid(id, dave);
        DreggLaunchToken tok = DreggLaunchToken(pad.tokenOf(id));
        console.log("  alice tokens (400e18) :", tok.balanceOf(alice));
        console.log("  carol tokens (200e18) :", tok.balanceOf(carol));
        console.log("  dave  tokens (0, lost):", tok.balanceOf(dave));
        require(tok.balanceOf(alice) == 400 * pad.TOKEN_UNIT(), "demo: alice full fill");
        require(tok.balanceOf(carol) == 200 * pad.TOKEN_UNIT(), "demo: carol marginal fill");
        require(tok.balanceOf(dave) == 0, "demo: dave below-clearing, no fill");

        // (e) GRADUATION — seed a provably-solvent pool with the disclosed fraction
        //     of the raise (50% of 3000 gwei proceeds + 100 tokens), then a live
        //     trade against the never-insolvent pool.
        _graduateAndTrade(pad, id, alice);

        vm.prank(creator);
        pad.withdrawProceeds(id);
        console.log("  creator remainder (wei):", uint256(3 * G * 1000) / 2);
        console.log(">> DEMO LAUNCH cleared fairly + GRADUATED to a provably-solvent market.");
    }

    /// The graduation demo, factored out to keep `run`'s stack shallow.
    function _graduateAndTrade(DreggLaunchpad pad, uint256 id, address alice) internal {
        (uint256 qSeed, uint256 tSeed) = pad.graduationSeed(id);
        require(qSeed == (3 * G * 1000) / 2, "demo: quote seed = 50% of proceeds");
        require(tSeed == 100 * pad.TOKEN_UNIT(), "demo: token seed = poolAllocation");
        address pool = pad.graduate(id, qSeed, tSeed);
        console.log("  graduated pool        :", pool);
        DreggSolventPool p = DreggSolventPool(pool);
        (uint256 rq, uint256 rt) = p.reserves();
        console.log("  pool quote reserve    :", rq);
        console.log("  pool token reserve    :", rt);
        console.log("  spot wei/token        :", p.spotPriceWeiPerToken());

        vm.deal(alice, 1 ether);
        vm.prank(alice);
        uint256 got = p.buy{value: 100 * G}(0);
        console.log("  alice bought (tokens) :", got);
    }

    function _commit(DreggLaunchpad pad, uint256 id, address who, uint256 price, uint256 qty, bytes32 salt)
        internal
    {
        bytes32 seal = pad.sealOf(price, qty, salt, who);
        vm.prank(who);
        pad.commitBid{value: price * qty}(id, seal, "");
    }
}
