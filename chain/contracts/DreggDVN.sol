// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDreggPeerRegistry} from "./IDreggPeerRegistry.sol";
import {IReceiveUln} from "./ILayerZeroDVN.sol";

/// A LayerZero V2 Decentralized Verifier Network (DVN) adapter backed by a dregg
/// light-client proof.
///
/// Where a default DVN attests a packet on a committee's say-so, `DreggDVN`
/// attests iff a dregg peer-finality proof covers the payload: the payload's
/// commitment must be included under the FINALIZED ROOT of the packet's SOURCE
/// chain that `DreggPeerRegistry` has PROVEN (by verifying that chain's
/// light-client-STARK-Groth16 on-chain). This upgrades the DVN from "M-of-N
/// signed" to "backed by a real light-client proof", so a stack requiring dregg
/// as one of its DVNs gains a proof-carrying conjunctive factor.
///
/// ## What changed (from INERT stub to a REAL binding)
///
/// The prior version gated on `DreggSettlement.isProvenMessageRoot`, which is
/// FAIL-CLOSED forever, so the DVN attested NOTHING. This version binds against
/// the PEER-VERIFICATION surface (`DreggPeerRegistry.isProvenPeerRoot`), whose
/// roots ARE provable today. The DVN is now LIVE: it attests a payload iff it is
/// Merkle-included under a genuinely-proven source-chain root.
///
/// ## The verification schema
///
/// `attestPayload` accepts iff BOTH hold:
///   1. `peers.isProvenPeerRoot(srcChainId, root)` — the claimed root was proven
///      as a finalized root of chain `srcChainId` (any historical height; a
///      superseded root still verifies, matching the dispatch-time semantics).
///   2. `payloadHash` is included under `root` via a keccak sorted-pair Merkle path.
/// Only then does it call `receiveUln.verify`. Every other path reverts and the
/// receive-library is never told anything (fail closed).
///
/// ## Hashing + NAMED RESIDUAL (the inclusion structure, honest)
///
/// The Merkle tree is keccak256 because this is the EVM boundary (keccak is the
/// native ~30-gas opcode; dregg's Poseidon2/BLAKE3 cost ~50-100x on-chain).
/// Gate (2)'s keccak-binary inclusion is SOUND when the proven peer root `root`
/// is itself a keccak message-commitment root the peer light-client proof
/// exposes; if the pinned peer VK instead attests a finalized EXECUTION STATE
/// root, message inclusion requires an MPT storage proof under that state root.
/// The binding STRUCTURE is real and live against the peer surface; which of the
/// two the pinned peer VK commits is the residual — stated, not hidden (see
/// `DreggProofISM` and `docs/deos/INTERCHAIN-ADAPTERS-DESIGN.md`).
///
/// ## THE NOMAD LAW (hard constraint)
///
/// Nomad's $190M hack accepted every UNPROVEN message because an uninitialized
/// slot defaulted to "accepted". This adapter's accept path REJECTS the
/// zero/default input: `root == 0` (the value a defaulted or empty
/// `proofMetadata` decodes to) fails check (1) because
/// `DreggPeerRegistry.isProvenPeerRoot(_, 0)` is false by construction — so the
/// revert happens BEFORE any inclusion work and BEFORE `receiveUln.verify` could
/// ever be reached. `test_Nomad_ZeroRootRejected` proves exactly that polarity.
///
/// ## Leaf commitment (documented choice)
///
/// The Merkle leaf is `payloadHash` itself: the DVN proves the payload's own
/// commitment is included under the proven source root. The `(packetHeader,
/// payloadHash)` binding is enforced downstream — `IReceiveUln.verify` keys the
/// DVN's attestation by exactly that pair, so a proof for one payload cannot be
/// laundered onto another header at the receive-library boundary.
contract DreggDVN {
    // ------------------------------------------------------------------
    // Errors (every reject path is typed; the adapter fails closed)
    // ------------------------------------------------------------------

    /// The peer-registry address pinned at construction has no code.
    error PeerRegistryHasNoCode(address registry);

    /// The receive-library address pinned at construction has no code.
    error ReceiveUlnHasNoCode(address receiveUln);

    /// THE NOMAD LAW: `(srcChainId, root)` was not proven by the peer registry
    /// (`isProvenPeerRoot` returned false — includes the zero/default root and a
    /// root proven only under a DIFFERENT chain).
    error RootNotProven(uint256 srcChainId, bytes32 root);

    /// The Merkle path did not reconstruct to `root`: the payload is not included
    /// under the proven source root (tampered proof, wrong leaf, or wrong siblings).
    error InclusionProofFailed(bytes32 computedRoot, bytes32 root);

    // ------------------------------------------------------------------
    // Events
    // ------------------------------------------------------------------

    /// A payload was attested (the receive-library's `verify` was called). This
    /// is the receipt: it names the proven source root, the payload, and the
    /// source chain the proof covered.
    event PayloadAttested(
        uint256 indexed srcChainId,
        bytes32 indexed root,
        bytes32 indexed payloadHash,
        uint64 confirmations,
        uint256 leafIndex
    );

    // ------------------------------------------------------------------
    // Pins (both fail-closed: a codeless address is never accepted)
    // ------------------------------------------------------------------

    /// The dregg peer-verification registry whose proven roots gate attestation.
    IDreggPeerRegistry public immutable peers;

    /// The LayerZero receive-library this DVN reports its attestation to.
    IReceiveUln public immutable receiveUln;

    constructor(IDreggPeerRegistry peers_, IReceiveUln receiveUln_) {
        // A staticcall/call to a codeless address "succeeds" silently on the EVM —
        // the exact fail-open shape the census flagged. Pin only live contracts
        // (fail closed), mirroring `DreggPeerRegistry`'s constructor.
        if (address(peers_).code.length == 0) {
            revert PeerRegistryHasNoCode(address(peers_));
        }
        if (address(receiveUln_).code.length == 0) {
            revert ReceiveUlnHasNoCode(address(receiveUln_));
        }
        peers = peers_;
        receiveUln = receiveUln_;
    }

    // ------------------------------------------------------------------
    // Attestation (permissionless: anyone holding a valid proof may submit)
    // ------------------------------------------------------------------

    /// Attest `payloadHash` for the packet `packetHeader` iff a dregg peer-finality
    /// proof covers it. `proofMetadata` is
    /// `abi.encode(uint256 srcChainId, bytes32 root, bytes32[] merkleProof,
    /// uint256 leafIndex)`.
    ///
    /// Reverts (and never calls `receiveUln.verify`) unless BOTH the proven-root
    /// gate and the inclusion proof hold. See the contract docs for THE NOMAD LAW.
    function attestPayload(
        bytes calldata packetHeader,
        bytes32 payloadHash,
        uint64 confirmations,
        bytes calldata proofMetadata
    ) external {
        (
            uint256 srcChainId,
            bytes32 root,
            bytes32[] memory merkleProof,
            uint256 leafIndex
        ) = abi.decode(proofMetadata, (uint256, bytes32, bytes32[], uint256));

        // (1) THE NOMAD LAW. An unproven or zero/default root is never accepted.
        // `isProvenPeerRoot(_, 0)` is false, so a defaulted `proofMetadata`
        // (root == 0) reverts HERE, before any inclusion work and before the
        // receive-library is ever consulted.
        if (!peers.isProvenPeerRoot(srcChainId, root)) {
            revert RootNotProven(srcChainId, root);
        }

        // (2) Inclusion: the payload's commitment must climb to the proven source
        // root via the keccak sorted-pair path.
        bytes32 computed = _computeRoot(payloadHash, merkleProof);
        if (computed != root) {
            revert InclusionProofFailed(computed, root);
        }

        // Both hold: attest. This is the ONLY call to the receive-library, and it
        // is unreachable on any reject path above.
        receiveUln.verify(packetHeader, payloadHash, confirmations);

        emit PayloadAttested(srcChainId, root, payloadHash, confirmations, leafIndex);
    }

    // ------------------------------------------------------------------
    // Merkle (keccak sorted-pair; position-independent)
    // ------------------------------------------------------------------

    /// Reconstruct the Merkle root from `leaf` and its `proof` siblings using the
    /// sorted-pair rule at each level. An empty proof reconstructs to the leaf
    /// itself (the minimal single-leaf inclusion). A single flipped or extra
    /// sibling yields a different root, which fails the `== root` check in the
    /// caller (proven by the tampered-proof reject test).
    function _computeRoot(bytes32 leaf, bytes32[] memory proof)
        internal
        pure
        returns (bytes32)
    {
        bytes32 h = leaf;
        for (uint256 i = 0; i < proof.length; i++) {
            h = _hashPair(h, proof[i]);
        }
        return h;
    }

    /// keccak256 of the two nodes in ascending order (sorted-pair), so the proof
    /// need not carry per-level left/right position bits.
    function _hashPair(bytes32 a, bytes32 b) internal pure returns (bytes32) {
        return a < b
            ? keccak256(abi.encodePacked(a, b))
            : keccak256(abi.encodePacked(b, a));
    }
}
