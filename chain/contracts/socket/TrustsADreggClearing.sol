// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDreggVerifier, DreggAttestation} from "./DreggVerifier.sol";

/// @title TrustsADreggClearing — a DEMO third-party consumer of a DREGG
///        attestation ("an external L2/DEX leverages DREGG's security").
///
/// This is a small, self-contained contract that DOES NOT live on DREGG and
/// keeps its OWN state — the concrete "DREGG as a security provider you plug
/// into, not a chain you migrate to." It imports the `DreggVerifier` socket and
/// gates its logic on a DREGG attestation: it will accept a clearing (and only
/// then let a trade settle against it) IF AND ONLY IF a DREGG proof attests the
/// clearing was a fair, conserved state transition of the DREGG instance this
/// contract trusts.
///
/// The trust decomposes into exactly two checks, both on-chain:
///   1. WHICH dregg — the attested `genesisRoot` must equal the trusted anchor
///      pinned at construction (this contract trusts ONE dregg instance; a
///      proof about a foreign dregg chain is refused before the pairing).
///   2. IS IT VALID — the socket's `verifyStatement` must return true (the real
///      BN254 pairing over the registry's current VK epoch). A forged or
///      tampered proof returns false → the trade is refused.
///
/// On accept it records the attested `finalRoot` as a trusted clearing and
/// unlocks settlement against it. That is the whole security-provider loop: an
/// external contract's economic action is gated on a DREGG proof, verified
/// where the external contract lives, with DREGG never custodying anything.
///
/// DEMO caveat: the socket it points at wraps a DEV-CEREMONY registry, so this
/// demonstrates the INTERFACE end-to-end, not production trust
/// (`docs/deos/OCIP-SECURITY-SOCKET.md`).
contract TrustsADreggClearing {
    /// The socket (VK-rotation-absorbing entry point). Immutable dependency.
    IDreggVerifier public immutable socket;

    /// The genesis anchor of the ONE dregg instance this contract trusts.
    /// A DREGG attestation whose `genesisRoot` differs is rejected outright.
    uint32[8] private _trustedAnchor;

    /// Clearings this contract has accepted (keyed by the attested final root).
    mapping(bytes32 => bool) public acceptedClearing;

    /// How many DREGG-attested clearings have been accepted (demo counter).
    uint256 public clearingsAccepted;

    /// The most recent DREGG state this contract trusts as settled.
    bytes32 public latestTrustedRoot;

    event ClearingTrusted(
        bytes32 indexed finalRoot,
        uint32 numTurns,
        uint256 epochCheckedAgainst
    );
    event TradeSettled(bytes32 indexed againstRoot, address indexed trader, uint256 amount);

    error UntrustedDreggInstance(bytes32 attestedGenesis, bytes32 trustedAnchor);
    error AttestationRejected();
    error NoTrustedClearing(bytes32 root);

    constructor(IDreggVerifier socket_, uint32[8] memory trustedAnchor_) {
        socket = socket_;
        _trustedAnchor = trustedAnchor_;
    }

    function trustedAnchor() external view returns (uint32[8] memory) {
        return _trustedAnchor;
    }

    /// THE SECURITY-PROVIDER GATE. Accept a DREGG-attested clearing.
    ///
    /// Reverts unless (1) the attestation is about the trusted dregg instance
    /// and (2) the DREGG proof verifies through the socket. On success the
    /// attested `finalRoot` becomes a trusted clearing this contract will
    /// settle trades against.
    function acceptClearing(
        DreggAttestation.Proof calldata proof,
        DreggAttestation.Statement calldata statement
    ) external returns (bytes32 finalRoot) {
        // 1. WHICH dregg — must be the instance we trust.
        bytes32 attestedGenesis = DreggAttestation.packLanes(statement.genesisRoot);
        bytes32 anchor = DreggAttestation.packLanes(_trustedAnchor);
        if (attestedGenesis != anchor) {
            revert UntrustedDreggInstance(attestedGenesis, anchor);
        }

        // 2. IS IT VALID — the real DREGG proof, verified through the socket
        //    against the current VK epoch. A forged proof returns false here.
        if (!socket.verifyStatement(proof, statement)) {
            revert AttestationRejected();
        }

        // Gated logic: record the DREGG-attested clearing.
        finalRoot = DreggAttestation.packLanes(statement.finalRoot);
        acceptedClearing[finalRoot] = true;
        latestTrustedRoot = finalRoot;
        clearingsAccepted += 1;
        emit ClearingTrusted(finalRoot, statement.numTurns, socket.currentEpoch());
    }

    /// A downstream economic action that is ONLY permitted against a clearing
    /// DREGG has attested. This is the "external contract's logic gated on the
    /// attestation" — it reverts if `againstRoot` was never DREGG-attested.
    function settleTrade(bytes32 againstRoot, uint256 amount) external {
        if (!acceptedClearing[againstRoot]) {
            revert NoTrustedClearing(againstRoot);
        }
        // (Demo: a real DEX would move escrowed funds at the attested price
        // here. The point is the GATE — no trade without a DREGG attestation.)
        emit TradeSettled(againstRoot, msg.sender, amount);
    }
}
