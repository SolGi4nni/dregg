// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// dregg whole-history settlement verifier (25-lane proof shape, post-v11).
///
/// Verifies a Groth16(BN254) proof that wraps the dregg recursive STARK
/// (`circuit-prove/src/ivc_turn_chain.rs::WholeChainProof`) attesting
/// "all finalized turns executed correctly, in order, and the state root
/// advanced from genesisRoot to finalRoot", then advances the on-chain
/// proven root.
///
/// The wrapped proof's circuit IS the STARK verifier
/// (`verify_turn_chain_recursive_from_parts`): the VK-fingerprint pin, the
/// fork batch-STARK FRI verification, and the segment tooth binding the
/// exposed `[first_old, last_new, count, acc]` to these public inputs.
///
/// ## The 25-lane public-input contract (pinned)
///
/// The whole-chain claim is 25 BabyBear lanes, in this exact order:
///
///   [0..8)   genesis_root  — `[BabyBear; 8]` (SEG_ANCHOR_WIDTH = 8)
///   [8..16)  final_root    — `[BabyBear; 8]`
///   [16]     num_turns     — 1 lane
///   [17..25) chain_digest  — `[BabyBear; 8]` (SEG_DIGEST_WIDTH = 8)
///
/// Every lane is a canonical BabyBear residue: strictly less than
/// p = 2^31 - 2^27 + 1 = 2013265921 (0x78000001). `settle` rejects any
/// non-canonical lane before touching the verifier.
///
/// ## Settlement state machine (on-chain twin of `dregg-bridge::ethereum`)
///
/// Mirrors `EthBridgeState` + `submit_eth_settlement`
/// (`bridge/src/ethereum.rs`): the first accepted settle establishes the
/// genesis anchor; every later settle must CHAIN — its `genesisRoot` lanes
/// must equal the current proven root (the previous proof's `finalRoot`) —
/// and height is strictly monotone (`numTurns >= 1`, provenHeight
/// accumulates). Note the continuity rule is the Rust bridge's
/// (proof genesis == current proven root), i.e. proofs are chained spans,
/// not repeated whole-history re-proofs from the original anchor.
interface IDreggSettlement {
    // ------------------------------------------------------------------
    // Errors (all reject paths are typed; the contract fails closed)
    // ------------------------------------------------------------------

    /// The verifier address pinned at construction has no code.
    error VerifierHasNoCode(address verifier);

    /// The expected verifying-key hash pinned at construction is zero.
    error ZeroVerifyingKeyHash();

    /// Lane `laneIndex` (in the pinned 25-lane order) carries `value`,
    /// which is not a canonical BabyBear residue (`value >= 2013265921`).
    error NonCanonicalLane(uint256 laneIndex, uint32 value);

    /// `numTurns == 0`: height would not strictly advance.
    error ZeroTurns();

    /// The submitted proof's genesisRoot does not chain from the current
    /// proven root. Both sides are keccak-packed lane digests.
    error ContinuityBroken(bytes32 expectedGenesis, bytes32 gotGenesis);

    /// The Groth16 verifier returned false for the pairing check.
    error ProofRejected();

    /// A non-zero `outboundMessageRoot` was submitted, but the 25-lane proof
    /// does not (yet) bind any outbound-message commitment — so the contract
    /// REFUSES to record it (fail closed). The former behavior (record the
    /// operator-supplied value alongside a valid settlement) let an operator
    /// attest an ARBITRARY message root and thereby forge cross-chain message
    /// inclusion through the ISM/DVN adapters; that path is now dead. The slot
    /// stays in the ABI for the proof-bound leg (apex message-commitment
    /// lanes), at which point `settle` will accept a root it can CHECK against
    /// the proof's public inputs.
    error MessageRootNotProofBound(bytes32 messageRoot);

    // ------------------------------------------------------------------
    // Events
    // ------------------------------------------------------------------

    /// A settlement was accepted. Roots are keccak256 over the 32-byte
    /// big-endian packing of the 8 lanes (lane i at bytes [4i, 4i+4));
    /// `height` is the new cumulative proven height.
    event Settled(bytes32 indexed oldRoot, bytes32 indexed newRoot, uint64 height);

    /// The raw lanes of an accepted settlement (full 25-lane statement).
    event SettledLanes(
        uint32[8] genesisRoot,
        uint32[8] finalRoot,
        uint32 numTurns,
        uint32[8] chainDigest
    );

    // ------------------------------------------------------------------
    // Views
    // ------------------------------------------------------------------

    /// True iff `root` (a `packLanes` key) has ever been proven by this contract
    /// (any historical proven root + the genesis anchor). `isProvenRoot(0)` is
    /// always false. Cross-chain verifiers gate message acceptance on this so a
    /// message proven under a since-superseded root still verifies.
    function isProvenRoot(bytes32 root) external view returns (bool);

    /// True iff `messageRoot` is a PROOF-BOUND outbound-message commitment
    /// recorded by a settlement. Adapters (Hyperlane ISM, LayerZero DVN) gate
    /// message inclusion on this. FAIL-CLOSED TODAY: the 25-lane proof does not
    /// yet carry an outbound-message commitment, `settle` refuses non-zero
    /// message roots (`MessageRootNotProofBound`), and this returns false for
    /// EVERY input — no operator-attested root can ever satisfy an adapter.
    /// The former operator-attested recording path is removed.
    function isProvenMessageRoot(bytes32 messageRoot) external view returns (bool);

    /// Current proven dregg state root, as keccak256 of the tightly packed
    /// 8 big-endian uint32 lanes (for indexing / event correlation).
    /// bytes32(0) until the first settle.
    function provenRoot() external view returns (bytes32);

    /// Current proven dregg state root as raw BabyBear lanes.
    function provenRootLanes() external view returns (uint32[8] memory);

    /// The genesis anchor (established by the first accepted settle), as the
    /// keccak-packed digest of its 8 lanes. bytes32(0) until established.
    function genesisAnchor() external view returns (bytes32);

    /// The genesis anchor as raw BabyBear lanes.
    function genesisAnchorLanes() external view returns (uint32[8] memory);

    /// Whether the first settle has established the genesis anchor.
    function genesisEstablished() external view returns (bool);

    /// Current proven height (cumulative finalized turns; strictly monotone).
    function provenHeight() external view returns (uint64);

    /// keccak256 of the Groth16 verifying key this contract checks against —
    /// the on-chain commitment to `EthSettlementProof.verifying_key_hash`.
    /// (The VK itself is baked into the IGroth16Verifier25 implementation;
    /// this hash lets off-chain tooling cross-check the deployment.)
    function verifyingKeyHash() external view returns (bytes32);

    // ------------------------------------------------------------------
    // Settlement
    // ------------------------------------------------------------------

    /// Submit a settlement.
    /// @param a,b,c       Groth16 proof points (BN254): a in G1, b in G2,
    ///                    c in G1. Word order matches EIP-197 (B's imaginary
    ///                    coord first).
    /// @param commitments,commitmentPok The proof's Pedersen commitment (2
    ///                    words) + its proof of knowledge (2 words) — gnark
    ///                    MarshalSolidity words [8..12). Part of the PROOF
    ///                    (the wrap circuit's commit-based range checker),
    ///                    not of the settlement statement.
    /// @param genesisRoot The 8 anchor lanes the proof starts from. First
    ///                    settle: establishes the genesis anchor. Later
    ///                    settles: must equal the current proven root lanes.
    /// @param finalRoot   The 8 lanes of the new proven root on success.
    /// @param numTurns    Number of finalized turns folded (must be >= 1).
    /// @param chainDigest The 8 digest lanes committing to the ordered
    ///                    (old, new) root pairs.
    /// @param outboundMessageRoot RESERVED for the proof-bound outbound-message
    ///                    commitment (a keccak Merkle root over the span's
    ///                    cross-chain messages). MUST be bytes32(0) today: the
    ///                    25-lane proof carries no message commitment to check
    ///                    it against, so any non-zero value reverts with
    ///                    `MessageRootNotProofBound` (fail closed — the
    ///                    operator-attested recording path is removed).
    /// Reverts on any non-canonical lane, broken continuity, zero turns, or
    /// a failed pairing check.
    function settle(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint32[8] calldata genesisRoot,
        uint32[8] calldata finalRoot,
        uint32 numTurns,
        uint32[8] calldata chainDigest,
        bytes32 outboundMessageRoot
    ) external;
}
