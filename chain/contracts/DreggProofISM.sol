// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IInterchainSecurityModule} from "./IInterchainSecurityModule.sol";
import {IDreggSettlement} from "./IDreggSettlement.sol";

/// A Hyperlane Interchain Security Module backed by a dregg validity proof.
///
/// dregg's native interop role is the *verification backend*: it answers "did
/// message E really happen" by proof, not by committee vote. This ISM accepts a
/// message iff (1) the dregg OUTBOUND MESSAGE ROOT it was committed under has
/// been recorded on-chain by `DreggSettlement` alongside a settlement, and
/// (2) a Merkle inclusion proof shows the message's leaf under that root.
///
/// ## The commitment model (why a MESSAGE root, not the STATE root)
///
/// A dregg *state* root is `packLanes(...)` — a keccak of 8 Poseidon/BabyBear
/// lanes — under which no EVM contract can cheaply prove message inclusion. So
/// `DreggSettlement` records, per span, a separate keccak Merkle root over the
/// outbound messages (`isProvenMessageRoot`). A message's leaf is
/// `keccak256(_message)` (the exact bytes Hyperlane's mailbox delivers);
/// `verify` reconstructs that message root from the leaf + an authenticated
/// sibling path (position-indexed by `leafIndex`) and requires it to be one
/// `DreggSettlement` has recorded.
///
/// ⚠ SCOPE (honest, not laundered): the message→root leg is currently
/// OPERATOR-ATTESTED — `DreggSettlement.settle` records `outboundMessageRoot`
/// when a valid settlement proof lands, but the 25-lane proof does not yet BIND
/// the root to the actual messages. Making it fully proof-carrying is a
/// dregg-circuit residual (a 26th proof lane, or a keccak fold into
/// `chainDigest`). The proven-STATE half IS by-proof today; this leg is not yet.
///
/// ## Historical-root gate (why `isProvenMessageRoot`, historical not current)
///
/// A message is committed under the message root recorded AT DISPATCH TIME,
/// which by processing time is usually not the latest span. `isProvenMessageRoot`
/// returns true for ANY historical recorded message root, so a message proven
/// under a since-superseded root still verifies — and, crucially,
/// `isProvenMessageRoot(bytes32(0))` is ALWAYS false.
///
/// ## THE NOMAD LAW
///
/// Nomad lost $190M because an uninitialized slot defaulted to "accepted"
/// (`confirmAt[0x00] = 1`), so every unproven message verified. Here the accept
/// path's first gate is `settlement.isProvenMessageRoot(messageRoot)`: a zero/
/// default/unrecorded `messageRoot` returns false and we revert. The
/// `verify(zero)` rejection is proven by an explicit test.
contract DreggProofISM is IInterchainSecurityModule {
    /// The pinned dregg settlement verifier. Immutable — the trust anchor is
    /// fixed at deployment, never governance-swappable.
    IDreggSettlement public immutable settlement;

    /// Deployment-time fail-closed guard: no codeless settlement address.
    error SettlementHasNoCode(address settlement);

    /// The `messageRoot` in the metadata was never recorded by the pinned
    /// settlement contract (THE NOMAD LAW bites here for the zero/default root).
    error UnprovenRoot(bytes32 messageRoot);

    /// The Merkle path did not reconstruct the claimed (proven) root from the
    /// message leaf.
    error InclusionProofInvalid(bytes32 claimedRoot, bytes32 computedRoot);

    /// Pin the settlement contract. Fail closed: a codeless address (a staticcall
    /// to which "succeeds" returning empty) must never be pinned as the oracle.
    constructor(IDreggSettlement settlement_) {
        if (address(settlement_).code.length == 0) {
            revert SettlementHasNoCode(address(settlement_));
        }
        settlement = settlement_;
    }

    /// This contract's logic is the deliverable; the routing is an integration
    /// detail. We advertise `NULL` (the relayer supplies no metadata for this
    /// type): the proof metadata is carried out-of-band (self-relay), or in
    /// production the recipient advertises a `CCIP_READ` ISM whose off-chain
    /// callback fetches the same (dreggRoot, path, index) metadata with zero
    /// relayer changes. The `verify` semantics are identical either way.
    function moduleType() external pure returns (uint8) {
        return uint8(IInterchainSecurityModule.Types.NULL);
    }

    /// Accept `_message` iff a dregg settlement proof attests it.
    ///
    /// `_metadata` ABI-decodes to `(bytes32 messageRoot, bytes32[] merkleProof,
    /// uint256 leafIndex)`. Reverts (fail closed) on any failure; returns true
    /// only when BOTH the recorded-root gate and the inclusion proof hold.
    function verify(bytes calldata _metadata, bytes calldata _message)
        external
        view
        returns (bool)
    {
        (bytes32 messageRoot, bytes32[] memory merkleProof, uint256 leafIndex) =
            abi.decode(_metadata, (bytes32, bytes32[], uint256));

        // Gate 1 — THE NOMAD LAW. A zero/default/unrecorded message root is
        // rejected before the message is looked at. isProvenMessageRoot(0) false.
        if (!settlement.isProvenMessageRoot(messageRoot)) {
            revert UnprovenRoot(messageRoot);
        }

        // Gate 2 — inclusion. The message's leaf must sit under that message root.
        bytes32 leaf = keccak256(_message);
        bytes32 computed = _computeRoot(leaf, merkleProof, leafIndex);
        if (computed != messageRoot) {
            revert InclusionProofInvalid(messageRoot, computed);
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
