// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Script.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";
import {DreggGroth16VerifierUpgradeable} from "../contracts/DreggGroth16VerifierUpgradeable.sol";

/// @title DeployUpgradeableSettlement
/// @notice Deploys the dregg settlement stack with the UPGRADEABLE-VK REGISTRY
///         instead of the code-baked generated verifier, so a VK-epoch flip is
///         a transaction (`advanceEpoch`), not a redeploy:
///
///           1. DreggGroth16VerifierUpgradeable()          — epoch-0 seeded
///                                                            byte-identical to
///                                                            the live VK (no args)
///           2. DreggSettlement(registry, vkHash, genesis) — consumes the
///                                                            registry directly
///                                                            (it IS an
///                                                            IGroth16Verifier25)
///
///         The registry is a drop-in for the generated-verifier + adapter pair:
///         its `verifyProof` targets the current epoch, so `DreggSettlement`
///         needs no change and no separate adapter.
///
/// GATE (public/mainnet): after deploy, hand registry ownership to a governance
/// contract behind a timelock — `registry.transferOwnership(timelock)`. A
/// mutable VK with an EOA owner is an accept-anything backdoor; the timelock is
/// the load-bearing control. See docs/deos/UPGRADEABLE-VK-REGISTRY.md.
///
/// Dry-run: forge script script/DeployUpgradeableSettlement.s.sol:DeployUpgradeableSettlement
contract DeployUpgradeableSettlement is Script {
    bytes32 constant DEFAULT_VK_HASH = keccak256("dregg-settlement-vk-dev-setup");
    uint256 constant ANVIL_DEV_KEY =
        0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80;

    function run() external {
        uint256 deployerPk = vm.envOr("DEPLOYER_PRIVATE_KEY", ANVIL_DEV_KEY);
        bytes32 vkHash = vm.envOr("DREGG_VK_HASH", DEFAULT_VK_HASH);
        uint32[8] memory genesisRoot = _genesisAnchor();

        console.log("== dregg UPGRADEABLE-VK settlement deploy ==");
        console.log("chainId :", block.chainid);
        console.log("deployer:", vm.addr(deployerPk));

        vm.startBroadcast(deployerPk);

        // 1. the storage-VK registry verifier, epoch-0 seeded from the live VK.
        DreggGroth16VerifierUpgradeable registry = new DreggGroth16VerifierUpgradeable();
        // 2. the settlement contract consuming the registry (current epoch).
        DreggSettlement settlement = new DreggSettlement(
            IGroth16Verifier25(address(registry)), vkHash, genesisRoot
        );

        // OPTIONAL public/mainnet: transfer registry ownership to a timelock.
        address newOwner = vm.envOr("DREGG_VK_OWNER", address(0));
        if (newOwner != address(0)) {
            registry.transferOwnership(newOwner);
            console.log("registry ownership -> ", newOwner);
        }

        vm.stopBroadcast();

        console.log("-----------------------------------------------------------");
        console.log("DreggGroth16VerifierUpgradeable:", address(registry));
        console.log("  currentEpoch:", registry.currentEpoch());
        console.log("  owner       :", registry.owner());
        console.log("DreggSettlement                :", address(settlement));
        console.log("-----------------------------------------------------------");
        console.log("VK-epoch flip = registry.advanceEpoch(newVk) [onlyOwner]: a tx, not a redeploy.");
    }

    function _fixtureGenesis() internal pure returns (uint32[8] memory g) {
        g = [
            uint32(421210617), 1637814550, 431291584, 1953496675,
            369364366, 1006647231, 1866996710, 48274474
        ];
    }

    function _genesisAnchor() internal view returns (uint32[8] memory g) {
        uint256[] memory d = new uint256[](0);
        uint256[] memory lanes = vm.envOr("DREGG_GENESIS_ANCHOR", ",", d);
        if (lanes.length == 0) {
            return _fixtureGenesis();
        }
        require(lanes.length == 8, "DREGG_GENESIS_ANCHOR must be 8 lanes");
        for (uint256 i = 0; i < 8; i++) {
            require(lanes[i] < 2013265921, "genesis lane not canonical BabyBear");
            g[i] = uint32(lanes[i]);
        }
    }
}
