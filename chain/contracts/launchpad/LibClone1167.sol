// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title LibClone1167
/// @notice Canonical EIP-1167 minimal-proxy deployment (the OpenZeppelin v5
///         `Clones.clone` assembly, verbatim). A clone is a 45-byte proxy that
///         delegatecalls the implementation — creation costs ~41k gas instead of
///         the implementation's full code deposit (~713k for `DreggSolventPool`).
///         The proxy bytecode is immutable and holds the implementation address
///         inline; there is no admin, no upgrade path, no storage in the proxy
///         beyond the delegatecalled contract's own.
library LibClone1167 {
    error CloneFailed();

    /// Deploy an EIP-1167 minimal proxy for `implementation`. The bytes are the
    /// EIP-1167 specification's canonical creation code (10-byte deployer +
    /// 45-byte runtime with the implementation address inline), assembled
    /// transparently so they can be checked against the EIP byte-by-byte.
    function clone(address implementation) internal returns (address instance) {
        bytes memory code = abi.encodePacked(
            hex"3d602d80600a3d3981f3363d3d373d3d3d363d73", // creation + runtime prefix
            implementation,
            hex"5af43d82803e903d91602b57fd5bf3" // runtime suffix
        );
        assembly ("memory-safe") {
            instance := create(0, add(code, 0x20), mload(code))
        }
        if (instance == address(0)) revert CloneFailed();
    }
}
