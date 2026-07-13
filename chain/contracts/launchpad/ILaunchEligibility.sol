// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title ILaunchEligibility
/// @notice OPTIONAL bidder-eligibility gate for a dregg launch. If a launch pins
///         a gate, `commitBid` requires `eligible(...) == true` before accepting
///         a sealed bid.
///
/// THE ROBINHOOD COMPOSITION (the payoff, `docs/deos/DREGG-LAUNCHPAD-DESIGN.md`
/// §2.4 + `dregg-interchain-gov/tests/robinhood_inbound.rs`): an implementation
/// can gate participation on a PROVEN Robinhood-Chain holding — a real
/// `eth_getProof` over the holder's tokenized-stock balance slot (e.g. TSLA) on
/// Robinhood Chain (chainId 46630), verified through `eth-lightclient`'s EIP-1186
/// machinery into a `ProvenForeignHolding { chain: Evm(46630), asset: TSLA, .. }`.
/// dregg networks the PROOF, not the token — nothing is bridged or escrowed. The
/// gate then answers "this bidder holds >= N of a Robinhood-Chain asset" as a
/// math fact, non-custodially.
///
/// Honest scope: this interface is the WIRING seam (BUILT + tested via a mock,
/// both polarities). A concrete Robinhood-holdings gate wraps the inbound
/// light-client verdict; its trust anchor is the honest per-chain grade in
/// `robinhood_inbound.rs` (weak-subjectivity today, L1-rollup-anchored trustless
/// rung named-not-built). The launchpad treats the gate as a pluggable oracle.
interface ILaunchEligibility {
    /// @param launchId the launch being gated.
    /// @param bidder   the address attempting to commit a sealed bid.
    /// @param proof    opaque eligibility evidence (e.g. an encoded holdings
    ///                 attestation / inclusion proof), interpreted by the gate.
    /// @return true iff `bidder` is eligible to participate in `launchId`.
    function eligible(uint256 launchId, address bidder, bytes calldata proof)
        external
        view
        returns (bool);
}
