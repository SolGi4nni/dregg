// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IClearingAttestor
/// @notice OPTIONAL dregg-clearing-proof attestor for a launch's uniform-price
///         clearing. If a launch pins an attestor, `finalizeClearing` requires
///         it to attest that the (saleSupply, clearingPrice, bookCommit) the
///         contract COMPUTED on-chain is the dregg fair clearing.
///
/// ## The two fairness rungs (graded honestly, `DREGG-LAUNCHPAD-DESIGN.md` §2.2)
///
/// 1. REPLAYABLE (always on): the launchpad computes the uniform clearing price
///    on-chain from the revealed book by a permutation-checked descending sort
///    (no-drop / no-insert, mirroring `Market/Aggregation.lean`) + a marginal-fill
///    walk. Anyone re-derives it from public reveals. This faithfully IMPLEMENTS
///    the mechanism whose fairness is PROVED in Lean:
///      - `Market/Optimality.lean:130 uniform_price_no_arbitrage` (every leg
///        value-neutral at ONE price),
///      - `uniform_price_envy_free` (same-direction bidders clear at the same
///        rate) — i.e. every winner pays the SAME clearing price.
///
/// 2. PROVED (when an attestor is pinned): a genuine dregg Groth16 clearing proof
///    binds the computed clearing as public inputs and verifies on-chain — the
///    SAME settlement pattern as `DreggSettlement.settle` (verify a real dregg
///    proof through a pinned Groth16 verifier). This is the anti-fake tooth: the
///    fairness is not asserted, it is a verified proof.
///
/// Honest scope: this interface + the wiring are BUILT and tested (a mock
/// attestor, accept + reject polarities). A CONCRETE attestor that verifies a
/// real dregg-Groth16 clearing proof is the NAMED WELD — the auction's
/// revealed-book → `Market.aggregate` → clearing tower is PROVED in Lean, but its
/// proving pipeline (STARK apex → BN254 shrink → Groth16, as in
/// `chain/gnark`) is not yet wired to emit a clearing statement. Until it is, a
/// launch runs on rung 1 (REPLAYABLE) with the attestor slot open for rung 2.
interface IClearingAttestor {
    /// @param launchId     the launch whose clearing is being attested.
    /// @param saleSupply   the disclosed number of tokens sold in the raise.
    /// @param clearingPrice the uniform price the launchpad computed on-chain.
    /// @param bookCommit   a commitment to the revealed book the clearing ran over
    ///                     (keccak over the revealed (bidder, price, qty) tuples).
    /// @param proof        the dregg clearing proof (Groth16 calldata, opaque here).
    /// @return true iff the proof attests `clearingPrice` is dregg's fair uniform
    ///         clearing of `bookCommit` at `saleSupply`.
    function attestClearing(
        uint256 launchId,
        uint256 saleSupply,
        uint256 clearingPrice,
        bytes32 bookCommit,
        bytes calldata proof
    ) external view returns (bool);
}
