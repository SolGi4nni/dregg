// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggVault.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";

contract PassSP1VerifierGas {
    function verifyProof(bytes32, bytes calldata, bytes calldata) external pure {}
}

contract MiniSettlementGas {
    function isProvenRoot(bytes32 root) external pure returns (bool) {
        return root != bytes32(0);
    }
}

/// #5 — DreggVault gas-DoS. The old `_computeRoot` rebuilt the WHOLE note tree from
/// storage on every deposit (O(n) SLOADs + hashes), so `depositCount` growing
/// eventually pushed a deposit past the block gas limit (a permanent liveness
/// ceiling). The incremental fixed-depth Merkle tree makes each deposit
/// O(TREE_DEPTH) — CONSTANT — so deposit gas does not grow with `depositCount`.
contract DreggVaultMerkleGasTest is Test {
    DreggVault vault;
    PassSP1VerifierGas verifier;
    MiniSettlementGas settlement;

    function setUp() public {
        verifier = new PassSP1VerifierGas();
        settlement = new MiniSettlementGas();
        vault = new DreggVault(address(verifier), bytes32(uint256(0xabc)), IDreggSettlement(address(settlement)));
        vm.deal(address(this), 1_000 ether);
    }

    function _dep(uint256 i) internal returns (uint256 gasUsed) {
        bytes32 note = keccak256(abi.encode("note", i));
        uint256 g0 = gasleft();
        vault.depositETH{value: 1 wei}(note);
        gasUsed = g0 - gasleft();
    }

    /// Deposit gas at a HIGH count is not materially larger than at a LOW count —
    /// the ~256 deposits in between add no per-deposit cost. Under the old O(n)
    /// rebuild the later deposit would cost hundreds of extra leaf reads+hashes and
    /// the gap would grow without bound; here it stays within a small constant.
    function test_depositGasIsConstantInDepositCount() public {
        // Warm the low tree levels, then sample an early deposit.
        for (uint256 i = 0; i < 16; i++) {
            _dep(i);
        }
        uint256 gasEarly = _dep(16);

        // Grow the tree by a few hundred deposits, then sample a late deposit.
        for (uint256 i = 17; i < 272; i++) {
            _dep(i);
        }
        uint256 gasLate = _dep(272);

        emit log_named_uint("deposit gas @ count 16 ", gasEarly);
        emit log_named_uint("deposit gas @ count 272", gasLate);

        // O(1): the later deposit is no more than a small constant above the early
        // one (in fact usually CHEAPER, as more tree slots are warm). A generous
        // 20k slack absorbs occasional cold higher-level slots while still failing
        // hard if per-deposit cost scaled with the 256 intervening deposits.
        assertLe(gasLate, gasEarly + 20_000, "deposit gas must not grow with depositCount");

        // Absolute sanity bound: a single deposit stays far under the block gas
        // limit no matter how many notes precede it.
        assertLt(gasLate, 250_000, "deposit stays cheap");
        assertEq(vault.depositCount(), 273);
    }

    /// The tree still advances the root on every deposit (each note is distinct).
    function test_rootAdvancesEachDeposit() public {
        _dep(0);
        bytes32 r1 = vault.noteTreeRoot();
        _dep(1);
        bytes32 r2 = vault.noteTreeRoot();
        _dep(2);
        bytes32 r3 = vault.noteTreeRoot();
        assertTrue(r1 != r2 && r2 != r3 && r1 != r3, "distinct roots");
        assertTrue(r1 != bytes32(0));
    }
}
