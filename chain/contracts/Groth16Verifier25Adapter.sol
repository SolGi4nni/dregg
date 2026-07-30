// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IGroth16Verifier25} from "./IGroth16Verifier25.sol";
import {DreggSettlementVK} from "./DreggSettlementVK.sol";

/// Adapter from the gnark-GENERATED settlement verifier
/// (DreggGroth16Verifier25.sol, emitted by chain/gnark
/// settlement_snark_test.go via groth16 VerifyingKey.ExportSolidity) to the
/// bool-returning `IGroth16Verifier25` shape `DreggSettlement` consumes.
///
/// The generated contract's `verifyProof(uint256[8] proof,
/// uint256[2] commitments, uint256[2] commitmentPok, uint256[25] input)`
/// REVERTS on an invalid proof and returns nothing on success; this adapter
/// staticcalls it and maps revert -> false. Fail-closed notes:
///
///   - a CODELESS inner address would make the staticcall "succeed"; the
///     constructor refuses one (and `DreggSettlement`'s constructor
///     independently refuses a codeless adapter);
///   - the 8 proof words are forwarded in gnark `MarshalSolidity` order,
///     which is exactly a ++ b[0] ++ b[1] ++ c (EIP-197 word order).
contract Groth16Verifier25Adapter is IGroth16Verifier25 {
    error InnerVerifierHasNoCode(address inner);

    address public immutable inner;

    constructor(address inner_) {
        if (inner_.code.length == 0) revert InnerVerifierHasNoCode(inner_);
        inner = inner_;
    }

    function verifyProof(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint256[25] calldata publicInputs
    ) external view returns (bool) {
        uint256[8] memory proof = [
            a[0], a[1],
            b[0][0], b[0][1],
            b[1][0], b[1][1],
            c[0], c[1]
        ];
        (bool ok, ) = inner.staticcall(
            abi.encodeWithSignature(
                "verifyProof(uint256[8],uint256[2],uint256[2],uint256[25])",
                proof,
                commitments,
                commitmentPok,
                publicInputs
            )
        );
        return ok;
    }

    /// The digest of the verifying key this adapter's `inner` verifier checks
    /// against, recomputed on-chain from the key words by
    /// `DreggSettlementVK.digest()`.
    ///
    /// ⚠ NAMED RESIDUAL — READ THIS BEFORE TRUSTING IT ON THE STATIC PATH.
    /// The gnark-generated `DreggGroth16Verifier25.sol` bakes its VK into
    /// CONTRACT-PRIVATE `uint256 constant`s, which no other contract can read.
    /// So this returns the digest of `DreggSettlementVK`'s COPY of those
    /// words, and the equality of the two copies is established OFF-CHAIN, by
    /// `chain/codegen/check_consistency.sh` step [2/8] (a name-keyed diff of
    /// all 76 constants in both files) plus the `gen_verifiers.py --check`
    /// drift gate in step [1/8]. On-chain, this contract cannot prove that its
    /// `inner` verifier holds the key it names.
    ///
    /// `DreggGroth16VerifierUpgradeable` does NOT have this residual: its key
    /// lives in STORAGE, so its `vkDigest()` reads the very words its pairing
    /// consumes. That path's digest is self-evidencing; this one leans on the
    /// codegen gate. Prefer the registry where the distinction matters.
    function vkDigest() external pure returns (bytes32) {
        return DreggSettlementVK.digest();
    }
}
