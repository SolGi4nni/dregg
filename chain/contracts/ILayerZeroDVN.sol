// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Minimal slice of the LayerZero V2 receive-library surface that a
/// Decentralized Verifier Network (DVN) adapter depends on.
///
/// In LayerZero V2, a DVN's entire destination-side job is to decide WHETHER
/// to call the receive-library's `verify` for a given packet. "Any entity can
/// build a DVN as long as its schema can confirm the payloadHash." dregg's
/// schema (implemented in `DreggDVN`): a dregg settlement proof must cover the
/// payload — i.e. the payload's commitment is proven-included under a dregg
/// state root that `DreggSettlement` has attested. The DVN calls `verify`
/// ONLY once that schema confirms; otherwise it reverts (fail closed).
///
/// This interface is intentionally minimal — it pins only the one call
/// `DreggDVN` consumes, and is MOCKED in tests (the concrete receive-ULN is a
/// LayerZero deployment contract, not ours to model in full).
interface IReceiveUln {
    /// Record this DVN's attestation that the packet identified by
    /// `packetHeader` carries `payloadHash`, verified with at least
    /// `confirmations` confirmations. The receive-library keys the DVN's vote
    /// by exactly this `(packetHeader, payloadHash)` pair, so passing both here
    /// is what binds the header to the payload downstream of the DVN.
    ///
    /// A DVN MUST NOT call this unless its verification schema has confirmed
    /// the payload. Calling it is the DVN asserting "I attest this packet".
    function verify(
        bytes calldata packetHeader,
        bytes32 payloadHash,
        uint64 confirmations
    ) external;
}
