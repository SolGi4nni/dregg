// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggVault.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";
import {MockSP1Verifier, MockSettlement} from "./DreggVault.t.sol";

/// #8 — escrowRelease fill-proof cross-deployment replay. Two DreggVaults share the
/// same `programVkey`; before the fix a valid fill proof for vault A could be
/// replayed on vault B (or the same guest on another chain) to release a same-id
/// escrow there, because the fill public values
/// (valid,escrowId,token,amount,recipient,clearingRoot) carried no address/chainid.
/// The vault now folds `boundVault` + `boundChainId` into the checked fill statement
/// — the same class fixed for `withdraw` in #3.
contract DreggVaultEscrowBindingTest is Test {
    DreggVault vaultA;
    DreggVault vaultB;
    MockSP1Verifier verifier;
    MockSettlement settlement;

    bytes32 constant PROGRAM_VKEY = bytes32(uint256(0xBEEFBEEF)); // SHARED across A and B
    address constant RECIPIENT = address(0xD00D);
    bytes32 constant CLEARING_ROOT = bytes32(uint256(0xC1EA5));

    function setUp() public {
        verifier = new MockSP1Verifier(); // always "verifies" — the binding is enforced by the vault
        settlement = new MockSettlement();
        settlement.setProven(CLEARING_ROOT, true);
        // Two vaults, same verifier + same programVkey → same fill proof "verifies" at both.
        vaultA = new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(address(settlement)));
        vaultB = new DreggVault(address(verifier), PROGRAM_VKEY, IDreggSettlement(address(settlement)));
        assertTrue(address(vaultA) != address(vaultB), "distinct deployments");
    }

    /// Build a fill proof BOUND to `boundVault` + `boundChainId`.
    function _fillProof(
        address boundVault,
        uint256 boundChainId,
        bytes32 escrowId,
        uint256 amount,
        bytes32 clearingRoot
    ) internal pure returns (bytes memory) {
        bytes memory pv = abi.encode(
            true, escrowId, address(0), amount, RECIPIENT, clearingRoot, boundVault, boundChainId
        );
        return abi.encode(hex"1234", pv);
    }

    function _lock(DreggVault vault, bytes32 escrowId, uint256 amount) internal {
        vault.escrowDepositETH{value: amount}(block.timestamp + 1 days, escrowId);
    }

    /// A fill proof built FOR vault A releases at vault A.
    function test_fillAcceptedAtOwnVault() public {
        bytes32 id = keccak256("e");
        _lock(vaultA, id, 1 ether);

        bytes memory proof = _fillProof(address(vaultA), block.chainid, id, 1 ether, CLEARING_ROOT);
        vaultA.escrowRelease(id, RECIPIENT, proof);

        assertEq(RECIPIENT.balance, 1 ether);
        assertEq(uint256(vaultA.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Released));
    }

    /// The SAME fill proof (bound to vault A) is REJECTED at vault B — the deployment
    /// binding stops the cross-vault replay. Both vaults hold the same-id escrow so
    /// that only the address binding, not the escrow record, can be the reason.
    function test_fillForVaultARejectedAtVaultB() public {
        bytes32 id = keccak256("shared-id");
        _lock(vaultA, id, 1 ether);
        _lock(vaultB, id, 1 ether);

        bytes memory proof = _fillProof(address(vaultA), block.chainid, id, 1 ether, CLEARING_ROOT);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.VaultBindingMismatch.selector, address(vaultA), address(vaultB)
            )
        );
        vaultB.escrowRelease(id, RECIPIENT, proof);
        // Vault B's escrow is untouched — still Locked, funds not paid out.
        assertEq(uint256(vaultB.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Locked));
        assertEq(RECIPIENT.balance, 0);
    }

    /// A fill proof for vault B is symmetrically rejected at vault A.
    function test_fillForVaultBRejectedAtVaultA() public {
        bytes32 id = keccak256("shared-id-2");
        _lock(vaultA, id, 1 ether);
        _lock(vaultB, id, 1 ether);

        bytes memory proof = _fillProof(address(vaultB), block.chainid, id, 1 ether, CLEARING_ROOT);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.VaultBindingMismatch.selector, address(vaultB), address(vaultA)
            )
        );
        vaultA.escrowRelease(id, RECIPIENT, proof);
    }

    /// A fill proof bound to the right vault but a DIFFERENT chain id is rejected —
    /// the same-address guest deployed on another chain cannot be replayed here.
    function test_fillForWrongChainRejected() public {
        bytes32 id = keccak256("chain-e");
        _lock(vaultA, id, 1 ether);

        uint256 wrongChain = block.chainid + 1;
        bytes memory proof = _fillProof(address(vaultA), wrongChain, id, 1 ether, CLEARING_ROOT);

        vm.expectRevert(
            abi.encodeWithSelector(
                DreggVault.ChainBindingMismatch.selector, wrongChain, block.chainid
            )
        );
        vaultA.escrowRelease(id, RECIPIENT, proof);
        assertEq(uint256(vaultA.escrowStatus(id)), uint256(DreggVault.EscrowStatus.Locked));
    }

    receive() external payable {}
}
