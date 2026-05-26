// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Script.sol";
import "../contracts/DreggVault.sol";
import "../contracts/DreggCredentialGate.sol";

/// @title DeployDregg
/// @notice Deploys DreggVault and DreggCredentialGate to Base Sepolia.
///
/// Required environment variables:
///   DEPLOYER_PRIVATE_KEY   - Private key of the deployer (with Base Sepolia ETH)
///   SP1_VERIFIER_ADDRESS   - SP1 Verifier Gateway on Base Sepolia
///   DREGG_PROGRAM_VKEY     - Verification key for the dregg SP1 guest program
///
/// Usage:
///   forge script script/Deploy.s.sol --rpc-url base_sepolia --broadcast --verify
contract DeployDregg is Script {
    function run() external {
        uint256 deployerPk = vm.envUint("DEPLOYER_PRIVATE_KEY");
        address sp1Verifier = vm.envAddress("SP1_VERIFIER_ADDRESS");
        bytes32 programVkey = vm.envBytes32("DREGG_PROGRAM_VKEY");
        address deployer = vm.addr(deployerPk);

        console.log("Deployer:", deployer);
        console.log("SP1 Verifier Gateway:", sp1Verifier);
        console.log("Program VKey:");
        console.logBytes32(programVkey);

        vm.startBroadcast(deployerPk);

        // Deploy the shielded deposit/withdraw vault.
        DreggVault vault = new DreggVault(sp1Verifier, programVkey);

        // Deploy the credential gate (deployer is initial admin).
        DreggCredentialGate gate = new DreggCredentialGate(
            sp1Verifier,
            programVkey,
            deployer
        );

        vm.stopBroadcast();

        console.log("--------------------------------------------");
        console.log("DreggVault deployed at:         ", address(vault));
        console.log("DreggCredentialGate deployed at:", address(gate));
        console.log("--------------------------------------------");
        console.log("");
        console.log("Next steps:");
        console.log("  1. Verify contracts on BaseScan");
        console.log("  2. Set trusted federation roots on the gate");
        console.log("  3. Configure the dregg node with the vault address");
    }
}
