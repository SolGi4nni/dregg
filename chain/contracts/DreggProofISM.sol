// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IInterchainSecurityModule} from "./IInterchainSecurityModule.sol";
import {IDreggPeerRegistry} from "./IDreggPeerRegistry.sol";

/// A Hyperlane Interchain Security Module backed by a dregg light-client proof.
///
/// dregg's native interop role is the *verification backend*: it answers "did
/// message E really happen on chain X" by PROOF, not by committee vote. This ISM
/// accepts an INBOUND message iff:
///   (1) the FINALIZED ROOT of the message's SOURCE chain that it was committed
///       under has been PROVEN on-chain by `DreggPeerRegistry` — i.e. a
///       light-client-STARK-Groth16 established "chain srcChainId finalized root
///       R" — and
///   (2) a keccak Merkle inclusion proof shows the message's leaf under R.
///
/// ## What changed (from INERT stub to a REAL binding)
///
/// The prior version gated on `DreggSettlement.isProvenMessageRoot`, which is
/// FAIL-CLOSED forever (the 25-lane settlement proof carries no outbound-message
/// commitment), so the ISM attested NOTHING. This version binds against the
/// PEER-VERIFICATION surface (`DreggPeerRegistry.isProvenPeerRoot`), whose roots
/// ARE provable today: a peer chain's finalized root is established by verifying
/// that chain's light-client STARK on-chain. The ISM is now LIVE — it attests a
/// message iff it is Merkle-included under a genuinely-proven peer root.
///
/// ## NAMED RESIDUAL (the inclusion structure, honest — not laundered)
///
/// Gate (2) reconstructs a keccak BINARY-tree root from the message leaf. That
/// is SOUND when the proven peer root R is itself a keccak message-commitment
/// root (a keccak Merkle root over the source chain's outbound cross-chain
/// messages) that the peer light-client proof exposes as its committed root —
/// the peer-side twin of dregg's own outbound-message-root residual
/// (`DreggSettlement`, `docs/deos/INTERCHAIN-ADAPTERS-DESIGN.md`). If instead the
/// pinned peer VK attests a finalized EXECUTION STATE root, message inclusion
/// requires an MPT storage proof of the source mailbox's message tree under that
/// state root, not this keccak-binary fold. The binding STRUCTURE here is real
/// and live against the peer surface; which of the two the pinned peer VK commits
/// is the residual, and it is stated, not hidden. `DreggPeerRegistry` records
/// whichever the VK attests.
///
/// ## Historical-root gate
///
/// A message is committed under the root proven AT DISPATCH TIME, usually not the
/// peer's latest. `isProvenPeerRoot` returns true for ANY historical proven root
/// of that chain, so a message proven under a since-superseded root still
/// verifies — and `isProvenPeerRoot(chainId, bytes32(0))` is ALWAYS false.
///
/// ## THE NOMAD LAW
///
/// Nomad lost $190M because an uninitialized slot defaulted to "accepted". Here
/// the accept path's first gate is `peers.isProvenPeerRoot(srcChainId, root)`: a
/// zero/default/unrecorded `root` returns false and we revert. Proven by an
/// explicit `verify(zero)` test.
contract DreggProofISM is IInterchainSecurityModule {
    /// The pinned dregg peer-verification registry. Immutable — the trust anchor
    /// is fixed at deployment, never governance-swappable.
    IDreggPeerRegistry public immutable peers;

    /// Deployment-time fail-closed guard: no codeless registry address.
    error PeerRegistryHasNoCode(address registry);

    /// The `(srcChainId, root)` pair in the metadata was never proven by the
    /// pinned peer registry (THE NOMAD LAW bites here for the zero/default root
    /// and for a root proven only under a DIFFERENT chain).
    error UnprovenRoot(uint256 srcChainId, bytes32 root);

    /// The Merkle path did not reconstruct the claimed (proven) root from the
    /// message leaf.
    error InclusionProofInvalid(bytes32 claimedRoot, bytes32 computedRoot);

    /// Pin the peer registry. Fail closed: a codeless address (a staticcall to
    /// which "succeeds" returning empty) must never be pinned as the oracle.
    constructor(IDreggPeerRegistry peers_) {
        if (address(peers_).code.length == 0) {
            revert PeerRegistryHasNoCode(address(peers_));
        }
        peers = peers_;
    }

    /// This contract's logic is the deliverable; the routing is an integration
    /// detail. We advertise `NULL` (the relayer supplies no metadata for this
    /// type): the proof metadata is carried out-of-band (self-relay), or in
    /// production the recipient advertises a `CCIP_READ` ISM whose off-chain
    /// callback fetches the same (srcChainId, root, path, index) metadata with
    /// zero relayer changes. The `verify` semantics are identical either way.
    function moduleType() external pure returns (uint8) {
        return uint8(IInterchainSecurityModule.Types.NULL);
    }

    /// Accept `_message` iff a dregg peer-finality proof attests its source
    /// chain's committed root and the message is included under it.
    ///
    /// `_metadata` ABI-decodes to `(uint256 srcChainId, bytes32 root,
    /// bytes32[] merkleProof, uint256 leafIndex)`. Reverts (fail closed) on any
    /// failure; returns true only when BOTH the proven-root gate and the
    /// inclusion proof hold.
    function verify(bytes calldata _metadata, bytes calldata _message)
        external
        view
        returns (bool)
    {
        (
            uint256 srcChainId,
            bytes32 root,
            bytes32[] memory merkleProof,
            uint256 leafIndex
        ) = abi.decode(_metadata, (uint256, bytes32, bytes32[], uint256));

        // Gate 1 — THE NOMAD LAW. A zero/default/unrecorded (chainId, root) is
        // rejected before the message is looked at. isProvenPeerRoot(_, 0) false.
        if (!peers.isProvenPeerRoot(srcChainId, root)) {
            revert UnprovenRoot(srcChainId, root);
        }

        // Gate 2 — inclusion. The message's leaf must sit under that proven root.
        bytes32 leaf = keccak256(_message);
        bytes32 computed = _computeRoot(leaf, merkleProof, leafIndex);
        if (computed != root) {
            revert InclusionProofInvalid(root, computed);
        }

        return true;
    }

    /// Reconstruct a Merkle root from `leaf`, its authenticated sibling `proof`,
    /// and its `index` (position-indexed: bit i of `index` selects whether the
    /// sibling at level i is on the right (bit 0) or the left (bit 1)). keccak
    /// of the concatenated pair, in position order — NOT sorted, so the index is
    /// load-bearing and a wrong index yields a wrong root (rejection).
    function _computeRoot(bytes32 leaf, bytes32[] memory proof, uint256 index)
        internal
        pure
        returns (bytes32)
    {
        bytes32 node = leaf;
        uint256 idx = index;
        for (uint256 i = 0; i < proof.length; i++) {
            if (idx & 1 == 0) {
                // node is the left child; sibling on the right.
                node = keccak256(abi.encodePacked(node, proof[i]));
            } else {
                // node is the right child; sibling on the left.
                node = keccak256(abi.encodePacked(proof[i], node));
            }
            idx >>= 1;
        }
        return node;
    }
}
