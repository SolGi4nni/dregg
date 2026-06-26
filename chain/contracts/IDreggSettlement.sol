// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// dregg whole-chain settlement verifier.
///
/// Verifies a Groth16(BN254) proof that wraps the dregg recursive STARK
/// (`circuit-prove/src/ivc_turn_chain.rs::WholeChainProof`) attesting
/// "all finalized turns executed correctly, in order, and the state root
/// advanced from genesisRoot to finalRoot", then advances the on-chain
/// proven root.
///
/// The wrapped proof's circuit IS the STARK verifier
/// (`verify_turn_chain_recursive_from_parts`): the VK-fingerprint pin, the
/// fork batch-STARK FRI verification, and the segment tooth binding the
/// exposed `[first_old, last_new, count, acc]` to these four public inputs.
///
/// This interface is the on-chain twin of `dregg-bridge::ethereum`'s
/// `solidity_verifier_interface()` (`bridge/src/ethereum.rs`) and consumes
/// the calldata layout of `EthSettlementProof::to_calldata` / the `(A,B,C)`
/// slicing of `Groth16Calldata`. The four public inputs are the BabyBear
/// `WholeChainProof.{genesis_root, final_root, num_turns, chain_digest}`
/// re-encoded as EVM words (each BabyBear is 31-bit, embedding losslessly).
interface IDreggSettlement {
    /// Current proven dregg state root (the contract's settled state).
    function provenRoot() external view returns (bytes32);

    /// Current proven height (monotone).
    function provenHeight() external view returns (uint64);

    /// keccak256 of the Groth16 verifying key this contract checks against —
    /// the on-chain commitment to `EthSettlementProof.verifying_key_hash`.
    function verifyingKeyHash() external view returns (bytes32);

    /// Submit a settlement.
    /// @param a,b,c       Groth16 proof points (BN254): a in G1, b in G2, c in G1.
    ///                    Word order matches EIP-197 (B's imaginary coord first),
    ///                    sliced by `Groth16Calldata::from_proof_bytes`.
    /// @param genesisRoot Must equal the current provenRoot (continuity).
    /// @param finalRoot   The new proven root on success.
    /// @param numTurns    Number of finalized turns folded.
    /// @param chainDigest Digest over the ordered (old,new) root pairs.
    /// Reverts if the pairing check fails or genesisRoot != provenRoot.
    function settle(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        bytes32 genesisRoot,
        bytes32 finalRoot,
        uint64  numTurns,
        bytes32 chainDigest
    ) external;

    event Settled(bytes32 indexed oldRoot, bytes32 indexed newRoot, uint64 height);
}
