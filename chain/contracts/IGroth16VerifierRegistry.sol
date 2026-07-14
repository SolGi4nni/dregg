// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IGroth16Verifier25} from "./IGroth16Verifier25.sol";

/// The UPGRADEABLE-VK registry shape.
///
/// `DreggGroth16Verifier25` (the gnark-GENERATED verifier) bakes the
/// verifying key (α, β, γ, δ, the Pedersen commitment key, and the 27 IC
/// points) into contract CODE, so every VK-epoch flip (a GAP-flip, the
/// nullifier flip, a re-genesis) forces a full verifier + settlement redeploy.
/// This interface moves the VK into STORAGE, keyed by a VK EPOCH: a flip
/// becomes a single `advanceEpoch` transaction, not a redeploy.
///
/// A proof TARGETS an epoch and is checked against THAT epoch's stored VK —
/// so proofs minted under an old VK stay verifiable at their epoch after the
/// pointer advances. `verifyProof` (the `IGroth16Verifier25` drop-in) targets
/// the CURRENT epoch, so this contract is a drop-in for the generated
/// verifier + adapter pair in `DreggSettlement`'s consumer slot.
///
/// Public-input lane order is exactly `IGroth16Verifier25`'s pinned 25-lane
/// statement; the epoch selects only WHICH VK the pairing runs against.
interface IGroth16VerifierRegistry is IGroth16Verifier25 {
    /// The epoch a fresh `verifyProof` (and a fresh settlement) checks against.
    function currentEpoch() external view returns (uint256);

    /// True iff a VK has been written for `epoch` (via seed / advance / set).
    function isEpochSet(uint256 epoch) external view returns (bool);

    /// Run the BN254 pairing check for proof (a, b, c) against the 25-lane
    /// public-input vector, using the VK stored for `epoch`. Returns true iff
    /// the proof verifies against THAT epoch's VK (false on an unset epoch,
    /// a non-canonical public input, a failed precompile, or a pairing miss).
    function verifyProofAtEpoch(
        uint256 epoch,
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint256[25] calldata publicInputs
    ) external view returns (bool);
}
