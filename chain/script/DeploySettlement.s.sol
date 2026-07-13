// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Script.sol";
import {DreggSettlement} from "../contracts/DreggSettlement.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {IGroth16Verifier25} from "../contracts/IGroth16Verifier25.sol";
import {Groth16Verifier25Adapter} from "../contracts/Groth16Verifier25Adapter.sol";
import {Verifier as DreggGroth16Verifier25} from "../contracts/DreggGroth16Verifier25.sol";

/// @title DeploySettlement
/// @notice Deploys the dregg whole-history SETTLEMENT stack to Base-Sepolia
///         (chainId 84532), in the exact 3-step order the real-proof test
///         wires it (`chain/test/DreggSettlementRealProof.t.sol:76-83`):
///
///           1. DreggGroth16Verifier25()                    — gnark-generated,
///                                                            VK baked in (no args)
///           2. Groth16Verifier25Adapter(verifier)          — revert->false wrap
///           3. DreggSettlement(adapter, vkHash, genesis)   — genesis pinned at
///                                                            construction
///
///         After deploy (default on; auto-skipped if a non-fixture genesis is
///         pinned) it lands the REAL Groth16 fixture proof via `settle()` and
///         asserts the proven root/height advanced — the same accept-path the
///         Foundry RealProof suite exercises, now on the freshly deployed twin.
///
/// ============================ EMBER: ONE-COMMAND BROADCAST ==================
///
///   # 0. one-time: a funded Base-Sepolia deployer key + the RPC/etherscan env
///   export DEPLOYER_PRIVATE_KEY=0x<funded base-sepolia key>   # EMBER input #1
///   export BASE_SEPOLIA_RPC_URL=https://sepolia.base.org       # or your node
///   export ETHERSCAN_API_KEY=<basescan key>                    # for --verify
///
///   # 1. (optional) pin a REAL devnet genesis anchor instead of the fixture's.
///   #    8 canonical BabyBear lanes (< 2013265921), comma-separated.
///   #    EMBER input #2 — the one value only ember can choose (the devnet
///   #    instance's genesis root). If UNSET, defaults to the fixture's genesis
///   #    so the bundled real proof settles in the same broadcast (a full demo).
///   #    If SET to a real anchor, the fixture self-settle auto-skips (the
///   #    fixture proof only chains from the fixture genesis) — ember then
///   #    settles with a real proof produced from that devnet.
///   # export DREGG_GENESIS_ANCHOR=421210617,1637814550,...    # EMBER input #2
///
///   # 2. the broadcast (THIS is the ember/outward step — a real testnet tx):
///   forge script script/DeploySettlement.s.sol:DeploySettlement \
///       --rpc-url base_sepolia --broadcast --verify -vvv
///
/// Dry-run first (no key/tx needed — simulates + asserts the fixture settles):
///   forge script script/DeploySettlement.s.sol:DeploySettlement
///
/// HONEST NOTE: the broadcast + the funded key + the choice of genesis anchor
/// are the EMBER/outward step (DREGGFI-PREREQS.md step 3). This script is the
/// dry-run-verified plumbing that makes "point at a testnet tx" one command
/// away. Nothing here broadcasts on its own.
/// ===========================================================================
contract DeploySettlement is Script {
    /// The dev-ceremony VK pin (matches DreggSettlementRealProof.t.sol:25 and
    /// EthSettlementProof.verifying_key_hash). Override with DREGG_VK_HASH.
    bytes32 constant DEFAULT_VK_HASH = keccak256("dregg-settlement-vk-dev-setup");

    /// The well-known anvil dev key — used ONLY so a keyless dry-run can
    /// simulate. A real broadcast supplies DEPLOYER_PRIVATE_KEY.
    uint256 constant ANVIL_DEV_KEY =
        0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80;

    function run() external {
        // ---- deploy-time constants, parameterized for ember at broadcast ----
        uint256 deployerPk = vm.envOr("DEPLOYER_PRIVATE_KEY", ANVIL_DEV_KEY);
        bytes32 vkHash = vm.envOr("DREGG_VK_HASH", DEFAULT_VK_HASH);

        // The genesis anchor: 8 canonical BabyBear lanes. Default = the fixture's
        // genesis (so the bundled real proof settles in-band on a dry run / demo
        // broadcast); ember overrides with a real devnet anchor at broadcast.
        uint32[8] memory genesisRoot = _genesisAnchor();
        bool settleFixture =
            vm.envOr("DREGG_SETTLE_FIXTURE", true) && _isFixtureGenesis(genesisRoot);

        address deployer = vm.addr(deployerPk);
        console.log("== dregg settlement deploy (Base-Sepolia, chainId 84532) ==");
        console.log("chainId :", block.chainid);
        console.log("deployer:", deployer);
        console.log("vkHash  :");
        console.logBytes32(vkHash);
        console.log("genesis lanes:");
        for (uint256 i = 0; i < 8; i++) console.log("  ", genesisRoot[i]);

        vm.startBroadcast(deployerPk);

        // 1. the gnark-generated verifier (VK baked in, no constructor args).
        DreggGroth16Verifier25 verifier = new DreggGroth16Verifier25();
        // 2. the revert->false adapter wrapping it.
        Groth16Verifier25Adapter adapter =
            new Groth16Verifier25Adapter(address(verifier));
        // 3. the settlement contract, genesis pinned at construction.
        DreggSettlement settlement = new DreggSettlement(
            IGroth16Verifier25(address(adapter)), vkHash, genesisRoot
        );

        // Post-deploy: land the REAL fixture proof, so the broadcast both
        // deploys AND proves the deployed twin accepts a real settlement.
        if (settleFixture) {
            _settleFixtureProof(settlement);
        }

        vm.stopBroadcast();

        console.log("-----------------------------------------------------------");
        console.log("DreggGroth16Verifier25 :", address(verifier));
        console.log("Groth16Verifier25Adapter:", address(adapter));
        console.log("DreggSettlement        :", address(settlement));
        console.log("-----------------------------------------------------------");
        if (settleFixture) {
            console.log("fixture proof SETTLED. provenHeight:", settlement.provenHeight());
            console.log("provenRoot:");
            console.logBytes32(settlement.provenRoot());
        } else {
            console.log("fixture self-settle SKIPPED (custom genesis anchor).");
            console.log("Settle a real proof produced from THIS anchor's devnet.");
        }
    }

    // ------------------------------------------------------------------
    // Genesis anchor: env-parameterized, defaults to the fixture's genesis
    // ------------------------------------------------------------------

    function _fixtureGenesis() internal pure returns (uint32[8] memory g) {
        // The committed fixture's genesis_root (settlement_groth16.json).
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

    function _isFixtureGenesis(uint32[8] memory g) internal pure returns (bool) {
        uint32[8] memory f = _fixtureGenesis();
        for (uint256 i = 0; i < 8; i++) {
            if (g[i] != f[i]) return false;
        }
        return true;
    }

    // ------------------------------------------------------------------
    // The real-proof post-deploy assertion (mirrors RealProof.test_RealProofSettles)
    // ------------------------------------------------------------------

    /// The parsed real fixture proof + its 25-lane statement (grouped into a
    /// struct so the `settle` call site stays under the stack-depth limit).
    struct Fixture {
        uint256[2] a;
        uint256[2][2] b;
        uint256[2] c;
        uint256[2] commitments;
        uint256[2] commitmentPok;
        uint32[8] genesisRoot;
        uint32[8] finalRoot;
        uint32[8] chainDigest;
        uint32 numTurns;
    }

    function _settleFixtureProof(DreggSettlement settlement) internal {
        Fixture memory fx;
        string memory json = vm.readFile("test/fixtures/settlement_groth16.json");
        _parseProof(json, fx);
        _parseStatement(json, fx);

        settlement.settle(
            fx.a, fx.b, fx.c, fx.commitments, fx.commitmentPok,
            fx.genesisRoot, fx.finalRoot, fx.numTurns, fx.chainDigest, bytes32(0)
        );

        // Post-deploy assertions (script reverts -> broadcast fails if untrue).
        bytes32 packedFinal = settlement.packLanes(fx.finalRoot);
        require(settlement.provenRoot() == packedFinal, "post-deploy: provenRoot != finalRoot");
        require(settlement.provenHeight() == fx.numTurns, "post-deploy: provenHeight != numTurns");
        require(settlement.isProvenRoot(packedFinal), "post-deploy: finalRoot not recorded");
    }

    function _parseProof(string memory json, Fixture memory fx) internal pure {
        string[] memory proofWords = vm.parseJsonStringArray(json, ".proof");
        require(proofWords.length == 8, "proof must be 8 words");
        fx.a = [vm.parseUint(proofWords[0]), vm.parseUint(proofWords[1])];
        fx.b = [
            [vm.parseUint(proofWords[2]), vm.parseUint(proofWords[3])],
            [vm.parseUint(proofWords[4]), vm.parseUint(proofWords[5])]
        ];
        fx.c = [vm.parseUint(proofWords[6]), vm.parseUint(proofWords[7])];

        string[] memory cm = vm.parseJsonStringArray(json, ".commitments");
        fx.commitments = [vm.parseUint(cm[0]), vm.parseUint(cm[1])];
        string[] memory pok = vm.parseJsonStringArray(json, ".commitment_pok");
        fx.commitmentPok = [vm.parseUint(pok[0]), vm.parseUint(pok[1])];
    }

    function _parseStatement(string memory json, Fixture memory fx) internal pure {
        uint256[] memory g = vm.parseJsonUintArray(json, ".genesis_root");
        uint256[] memory f = vm.parseJsonUintArray(json, ".final_root");
        uint256[] memory d = vm.parseJsonUintArray(json, ".chain_digest");
        fx.numTurns = uint32(vm.parseJsonUint(json, ".num_turns"));
        for (uint256 i = 0; i < 8; i++) {
            fx.genesisRoot[i] = uint32(g[i]);
            fx.finalRoot[i] = uint32(f[i]);
            fx.chainDigest[i] = uint32(d[i]);
        }
    }
}
