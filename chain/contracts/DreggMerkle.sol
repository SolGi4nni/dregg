// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title DreggMerkle
/// @notice A POSITIONAL keccak256 Merkle-inclusion verifier — the EVM-sound
///         primitive for proving a fact about dregg state on-chain.
///
/// ## What it proves (and why it is sound with only the root)
///
/// Given a `root`, a `leaf`, its `index`, and its `siblings` (bottom-up), this
/// returns true iff recomputing the path from the leaf yields the root. Because
/// each internal node is `keccak256(left ++ right)` — collision-resistant and
/// binding on BOTH children — a forged leaf (or tampered sibling / wrong index)
/// cannot reach the same root except by a keccak collision. So an EVM contract
/// holding ONLY the root can soundly check inclusion; it needs neither the set
/// nor a trusted prover.
///
/// ## Why NOT the poly-eval accumulator (the honest contrast)
///
/// dregg's `commit/src/accumulator.rs` is an O(1) poly-eval accumulator over
/// BabyBear^4 (`Acc = prod(alpha - h_i)`). Its bare identity check
/// (`quotient*(alpha-x) [+ remainder] == Acc`) is SETLESS-FORGEABLE: over a
/// field, for ANY target `x != alpha` an attacker picks `quotient =
/// Acc*(alpha-x)^{-1}` (membership) or any nonzero `remainder'` with the matching
/// quotient (non-membership) and the identity passes — see the "Soundness scope"
/// note and `verify_non_membership_bound` in that file. Soundness there needs the
/// VERIFIER to hold the set (recompute f(x)), an in-circuit binding, or a
/// pairing-based commitment — none of which an EVM contract has cheaply. A
/// Merkle root binds every leaf with only the root, so it is the correct
/// on-chain inclusion primitive. (The accumulator remains dregg's IN-CIRCUIT /
/// set-holder non-membership tool; it is just not an on-chain verifier.)
///
/// ## Convention (fixed, matches dregg's positional `compress(left,right)`)
///
/// - node(l, r) = keccak256(abi.encodePacked(l, r))   [POSITIONAL, not sorted]
/// - proof walks bottom→top; at level i, if the current index bit is 0 the
///   sibling is the RIGHT child (`node(cur, sib)`), else the LEFT (`node(sib, cur)`).
/// - trees are built over a power-of-two leaf count (pad with `EMPTY_LEAF`), so
///   every node has a sibling — no odd-promotion ambiguity in proofs.
///
/// This mirrors the positional hashing dregg uses for its Merkle nodes
/// (`metatheory Dregg2.Circuit.StateCommit.compress` / `frameDigest`, and the
/// on-chain `DreggVault._insertLeaf` incremental note tree), instantiated with
/// keccak256 for an
/// EVM-native, EVM-cheap commitment (a dregg-published keccak MIRROR of a
/// BabyBear-native sub-root — the same construction as the outbound message
/// root; see `DreggStateOracle`).
library DreggMerkle {
    /// Domain-separated padding leaf for power-of-two completion.
    bytes32 internal constant EMPTY_LEAF = keccak256("dregg.merkle.empty.leaf.v1");

    /// @notice Verify a positional keccak Merkle inclusion proof.
    /// @param root     the Merkle root (a dregg sub-root, e.g. the nullifier or
    ///                 commitments root's keccak mirror).
    /// @param leaf     the leaf being proven present (already keccak-encoded).
    /// @param index    the leaf's 0-based position (fixes left/right at each level).
    /// @param siblings the sibling hashes bottom→top; length == tree depth.
    /// @return true iff `leaf` at `index` is included under `root`.
    function verifyInclusion(
        bytes32 root,
        bytes32 leaf,
        uint256 index,
        bytes32[] calldata siblings
    ) internal pure returns (bool) {
        // A path longer than 256 levels cannot address a distinct index bit and
        // is meaningless; bound it so `index` fully determines every turn.
        if (siblings.length > 256) return false;
        // If the index still has set bits above the proof height, it addresses a
        // level the proof does not cover — reject (prevents index/height mismatch).
        if (siblings.length < 256 && (index >> siblings.length) != 0) return false;

        bytes32 node = leaf;
        uint256 idx = index;
        for (uint256 i = 0; i < siblings.length; i++) {
            if (idx & 1 == 0) {
                node = keccak256(abi.encodePacked(node, siblings[i]));
            } else {
                node = keccak256(abi.encodePacked(siblings[i], node));
            }
            idx >>= 1;
        }
        return node == root;
    }

    /// @notice The canonical leaf encoding for a dregg 32-byte state element
    ///         (a nullifier, a note commitment, an (address,balance) balance leaf).
    ///         Hashing the raw element domain-separates leaves from internal
    ///         nodes (second-preimage hardening: an internal node is never a
    ///         valid leaf preimage).
    function encodeLeaf(bytes32 element) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(bytes1(0x00), element));
    }
}
