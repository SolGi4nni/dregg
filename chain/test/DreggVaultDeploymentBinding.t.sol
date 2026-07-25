// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggVault.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";

/// @dev SP1 verifier stand-in that always accepts (the binding is enforced by the
/// vault's public-value checks, not the mock — the mock models "the proof verified").
contract PassSP1Verifier {
    function verifyProof(bytes32, bytes calldata, bytes calldata) external pure {}
}

/// @dev Minimal settlement stand-in (constructor only needs it to have code).
contract MiniSettlement {
    function isProvenRoot(bytes32 root) external pure returns (bool) {
        return root != bytes32(0);
    }
}

/// #3 — withdraw proof cross-deployment replay. Two DreggVaults share the same
/// `programVkey`; before the fix a valid withdraw proof for vault A replayed on
/// vault B (or the same guest on another chain), because the public values
/// (valid,nullifier,token,amount,recipient,root) carried no address/chainid. The
/// vault now folds `boundVault` + `boundChainId` into the checked statement.
contract DreggVaultDeploymentBindingTest is Test {
    DreggVault vaultA;
    DreggVault vaultB;
    PassSP1Verifier verifier;
    MiniSettlement settlement;

    bytes32 constant PROGRAM_VKEY = bytes32(uint256(0xBEEFBEEF)); // SHARED across A and B
    address constant RECIPIENT = address(0xD00D);

    function setUp() public {
        verifier = new PassSP1Verifier();
        settlement = new MiniSettlement();
        // Two vaults, same verifier + same programVkey → same proof "verifies" at both.
        vaultA = new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(address(settlement)));
        vaultB = new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(address(settlement)));
        assertTrue(address(vaultA) != address(vaultB), "distinct deployments");
    }

    /// Build a withdraw proof BOUND to `boundVault` + `boundChainId`.
    function _proof(
        address boundVault,
        uint256 boundChainId,
        bytes32 nullifier,
        uint256 amount,
        bytes32 root
    ) internal pure returns (bytes memory) {
        bytes memory pv = abi.encode(
            true, nullifier, address(0), amount, RECIPIENT, root, boundVault, boundChainId
        );
        return abi.encode(hex"1234", pv);
    }

    /// A proof built FOR vault A is accepted at vault A.
    function test_proofAcceptedAtOwnVault() public {
        vaultA.depositETH{value: 1 ether}(keccak256("noteA"));

        bytes memory proof = _proof(address(vaultA), block.chainid, keccak256("nfA"), 0.5 ether, vaultA.noteTreeRoot());
        vaultA.withdraw(address(0), 0.5 ether, RECIPIENT, proof);

        assertEq(RECIPIENT.balance, 0.5 ether);
        assertTrue(vaultA.usedNullifiers(keccak256("nfA")));
    }

    /// The SAME proof (bound to vault A) is REJECTED at vault B — the deployment
    /// binding stops the cross-vault replay. Both vaults are funded so that only the
    /// address binding, not solvency or the root, can be the reason.
    function test_proofForVaultARejectedAtVaultB() public {
        vaultA.depositETH{value: 1 ether}(keccak256("noteA"));
        vaultB.depositETH{value: 1 ether}(keccak256("noteB"));

        bytes memory proof = _proof(address(vaultA), block.chainid, keccak256("nf"), 0.5 ether, vaultA.noteTreeRoot());

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.VaultBindingMismatch.selector, address(vaultA), address(vaultB)
            )
        );
        vaultB.withdraw(address(0), 0.5 ether, RECIPIENT, proof);
    }

    /// A proof for vault B is symmetrically rejected at vault A.
    function test_proofForVaultBRejectedAtVaultA() public {
        vaultA.depositETH{value: 1 ether}(keccak256("noteA"));
        vaultB.depositETH{value: 1 ether}(keccak256("noteB"));

        bytes memory proof = _proof(address(vaultB), block.chainid, keccak256("nf2"), 0.5 ether, vaultB.noteTreeRoot());

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.VaultBindingMismatch.selector, address(vaultB), address(vaultA)
            )
        );
        vaultA.withdraw(address(0), 0.5 ether, RECIPIENT, proof);
    }

    /// A proof bound to the right vault but a DIFFERENT chain id is rejected — the
    /// same-address guest deployed on another chain cannot be replayed here.
    function test_proofForWrongChainRejected() public {
        vaultA.depositETH{value: 1 ether}(keccak256("noteA"));

        uint256 wrongChain = block.chainid + 1;
        bytes memory proof = _proof(address(vaultA), wrongChain, keccak256("nfChain"), 0.5 ether, vaultA.noteTreeRoot());

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.ChainBindingMismatch.selector, wrongChain, block.chainid
            )
        );
        vaultA.withdraw(address(0), 0.5 ether, RECIPIENT, proof);
    }

    receive() external payable {}
}
