// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDreggSettlement} from "./IDreggSettlement.sol";
import {IReceiveUln} from "./ILayerZeroDVN.sol";

/// A LayerZero V2 Decentralized Verifier Network (DVN) adapter backed by a
/// dregg validity proof.
///
/// Where a default DVN attests a packet on a committee's say-so, `DreggDVN`
/// attests iff a dregg settlement covers the payload: the payload's commitment
/// must be included under a dregg OUTBOUND MESSAGE ROOT that `DreggSettlement`
/// recorded alongside its 25-lane Groth16 settlement. This upgrades the DVN
/// from "M-of-N signed" to "backed by a dregg settlement", so a stack that
/// requires dregg as one of its DVNs gains a conjunctive factor.
///
/// ## The verification schema
///
/// `attestPayload` accepts iff BOTH hold:
///   1. `settlement.isProvenMessageRoot(messageRoot)` — the claimed root was
///      recorded by a settlement (any historical span; a superseded root still
///      verifies, matching the dispatch-time semantics a cross-chain verifier
///      needs).
///   2. `payloadHash` is included under `messageRoot` via a keccak sorted-pair
///      Merkle path.
/// Only then does it call `receiveUln.verify`. Every other path reverts and
/// the receive-library is never told anything (fail closed).
///
/// ## Hashing (why keccak here, and the boundary — see INTERCHAIN-ADAPTERS-DESIGN.md)
///
/// The Merkle tree is keccak256 because this is the EVM boundary: keccak is the
/// native ~30-gas opcode, whereas dregg's core hashes (Poseidon2 algebraic,
/// BLAKE3 CPU) cost ~50-100x on-chain. This is NOT dregg's note/state tree
/// rehashed — it is a small purpose-built commitment over ONLY the outbound
/// cross-chain messages of a span, so it neither duplicates the dual-commitment
/// architecture nor imposes bulk rehashing. NAMED RESIDUAL: binding this root
/// inside the dregg proof is a hash-family DECISION (keccak-in-circuit vs a
/// Poseidon2 message root vs folding inclusion into the wrap) — see the design
/// doc; the settlement records it operator-attested until then.
///
/// ## THE NOMAD LAW (hard constraint — see INTERCHAIN-ADAPTERS-DESIGN.md)
///
/// Nomad's $190M hack accepted every UNPROVEN message because an uninitialized
/// slot defaulted to "accepted" (`confirmAt[0x00] = 1`). This adapter's accept
/// path REJECTS the zero/default/empty input: `messageRoot == 0` (the value a
/// defaulted or empty `proofMetadata` decodes to) fails check (1) because
/// `DreggSettlement.isProvenMessageRoot(0)` is false by construction — so the
/// revert happens BEFORE any inclusion work and BEFORE `receiveUln.verify` could
/// ever be reached. `test_Nomad_ZeroRootRejected` proves exactly that polarity.
///
/// ## Leaf commitment (documented choice)
///
/// The Merkle leaf is `payloadHash` itself: the DVN proves the payload's own
/// commitment is included under the recorded message root. The `(packetHeader,
/// payloadHash)` binding is enforced downstream — `IReceiveUln.verify` keys the
/// DVN's attestation by exactly that pair, so a proof for one payload cannot be
/// laundered onto another header at the receive-library boundary.
contract DreggDVN {
    // ------------------------------------------------------------------
    // Errors (every reject path is typed; the adapter fails closed)
    // ------------------------------------------------------------------

    /// The settlement address pinned at construction has no code.
    error SettlementHasNoCode(address settlement);

    /// The receive-library address pinned at construction has no code.
    error ReceiveUlnHasNoCode(address receiveUln);

    /// THE NOMAD LAW: `messageRoot` was not recorded by any settlement
    /// (`isProvenMessageRoot` returned false — includes the zero/default root).
    error RootNotProven(bytes32 messageRoot);

    /// The Merkle path did not reconstruct to `messageRoot`: the payload is not
    /// included under the recorded message root (tampered proof, wrong leaf, or
    /// wrong sibling set).
    error InclusionProofFailed(bytes32 computedRoot, bytes32 messageRoot);

    // ------------------------------------------------------------------
    // Events
    // ------------------------------------------------------------------

    /// A payload was attested (the receive-library's `verify` was called).
    event PayloadAttested(
        bytes32 indexed messageRoot,
        bytes32 indexed payloadHash,
        uint64 confirmations,
        uint256 leafIndex
    );

    // ------------------------------------------------------------------
    // Pins (both fail-closed: a codeless address is never accepted)
    // ------------------------------------------------------------------

    /// The dregg settlement contract whose recorded message roots gate attestation.
    IDreggSettlement public immutable settlement;

    /// The LayerZero receive-library this DVN reports its attestation to.
    IReceiveUln public immutable receiveUln;

    constructor(IDreggSettlement settlement_, IReceiveUln receiveUln_) {
        // A staticcall/call to a codeless address "succeeds" silently on the
        // EVM — the exact fail-open shape the census flagged. Pin only live
        // contracts (fail closed), mirroring `DreggSettlement`'s constructor.
        if (address(settlement_).code.length == 0) {
            revert SettlementHasNoCode(address(settlement_));
        }
        if (address(receiveUln_).code.length == 0) {
            revert ReceiveUlnHasNoCode(address(receiveUln_));
        }
        settlement = settlement_;
        receiveUln = receiveUln_;
    }

    // ------------------------------------------------------------------
    // Attestation (permissionless: anyone holding a valid proof may submit)
    // ------------------------------------------------------------------

    /// Attest `payloadHash` for the packet `packetHeader` iff a dregg
    /// settlement covers it. `proofMetadata` is
    /// `abi.encode(bytes32 messageRoot, bytes32[] merkleProof, uint256 leafIndex)`.
    ///
    /// Reverts (and never calls `receiveUln.verify`) unless BOTH the proven-root
    /// gate and the inclusion proof hold. See the contract docs for THE NOMAD
    /// LAW guarantee.
    function attestPayload(
        bytes calldata packetHeader,
        bytes32 payloadHash,
        uint64 confirmations,
        bytes calldata proofMetadata
    ) external {
        (bytes32 messageRoot, bytes32[] memory merkleProof, uint256 leafIndex) =
            abi.decode(proofMetadata, (bytes32, bytes32[], uint256));

        // (1) THE NOMAD LAW. An unrecorded or zero/default root is never
        // accepted. `isProvenMessageRoot(0)` is false in `DreggSettlement`, so a
        // defaulted `proofMetadata` (messageRoot == 0) reverts HERE, before any
        // inclusion work and before the receive-library is ever consulted.
        if (!settlement.isProvenMessageRoot(messageRoot)) {
            revert RootNotProven(messageRoot);
        }

        // (2) Inclusion: the payload's commitment must climb to the recorded
        // message root via the keccak sorted-pair path.
        bytes32 computed = _computeRoot(payloadHash, merkleProof);
        if (computed != messageRoot) {
            revert InclusionProofFailed(computed, messageRoot);
        }

        // Both hold: attest. This is the ONLY call to the receive-library, and
        // it is unreachable on any reject path above.
        receiveUln.verify(packetHeader, payloadHash, confirmations);

        emit PayloadAttested(messageRoot, payloadHash, confirmations, leafIndex);
    }

    // ------------------------------------------------------------------
    // Merkle (keccak sorted-pair; position-independent)
    // ------------------------------------------------------------------

    /// Reconstruct the Merkle root from `leaf` and its `proof` siblings using
    /// the sorted-pair rule at each level. An empty proof reconstructs to the
    /// leaf itself (the minimal single-leaf inclusion). A single flipped or
    /// extra sibling yields a different root, which fails the `== dreggRoot`
    /// check in the caller (proven by the tampered-proof reject test).
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

    /// keccak256 of the two nodes in ascending order (sorted-pair), so the
    /// proof need not carry per-level left/right position bits.
    function _hashPair(bytes32 a, bytes32 b) internal pure returns (bytes32) {
        return a < b
            ? keccak256(abi.encodePacked(a, b))
            : keccak256(abi.encodePacked(b, a));
    }
}
