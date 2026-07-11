// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Hyperlane Interchain Security Module interface (faithful to the Hyperlane
/// monorepo `contracts/interfaces/IInterchainSecurityModule.sol`).
///
/// An ISM is the per-recipient, permissionless verifier seam: a message
/// recipient names an ISM, and the mailbox will only deliver a message after
/// `ism.verify(metadata, message)` returns true. This is the ex-Celo/Optics
/// team's modular-security design — bring your own verifier, no governance.
///
/// dregg's `DreggProofISM` implements this: a message is accepted iff a dregg
/// settlement proof (checked on-chain by `DreggSettlement`) attests it.
interface IInterchainSecurityModule {
    /// The canonical Hyperlane module-type enum. The relayer builds metadata
    /// per this tag; only enum'd types get first-class metadata construction.
    /// `NULL` carries no relayer metadata (self-relay / off-path metadata),
    /// `CCIP_READ` routes arbitrary proof metadata via an off-chain callback
    /// with zero relayer changes — the two production routes for a proof-ISM.
    enum Types {
        UNUSED, // 0
        ROUTING, // 1
        AGGREGATION, // 2
        LEGACY_MULTISIG, // 3
        MERKLE_ROOT_MULTISIG, // 4
        MESSAGE_ID_MULTISIG, // 5
        NULL, // 6 — relayer supplies no metadata
        CCIP_READ // 7 — off-chain metadata via CCIP-read callback
    }

    /// Returns an enum that Hyperlane's off-chain agents use to decide how to
    /// construct metadata for `verify`.
    function moduleType() external view returns (uint8);

    /// Verify `_message` using `_metadata`. Non-view: an ISM may read/write
    /// state (e.g. verify one epoch proof then do cheap per-message lookups).
    /// MUST return true only for a genuinely attested message; a false return
    /// (or a revert) blocks delivery. THE NOMAD LAW: the zero/default input
    /// MUST NOT verify.
    function verify(bytes calldata _metadata, bytes calldata _message)
        external
        returns (bool);
}
