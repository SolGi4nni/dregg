// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDreggSettlement} from "./IDreggSettlement.sol";

/// @title DreggStateOracle
/// @notice An ORDERED, PROOF-BOUND INDEX of settled dregg state roots, plus the
///         eth→dregg instruction channel. Everything it answers is a function of
///         `DreggSettlement`; it holds no attestation of its own.
///
/// ## ⚑ WHAT THIS CONTRACT USED TO DO, AND WHY IT NO LONGER DOES (2026-07-28)
///
/// `recordEpoch(stateRoot, height, subRootVec)` wrote FOUR keccak "mirror" sub-roots
/// — balance, nullifier, commitments, heap — and a height, STRAIGHT TO STORAGE, with
/// exactly one thing checked: that `stateRoot` was `settlement.isProvenRoot`. Nothing
/// tied the sub-roots or the height to the state that was actually proven. On top of
/// that storage sat `proveHolding` / `proveNullifierSpent` / `proveCommitmentExists`
/// / `verifyAgainstSubRoot`, whose keccak Merkle check is sound *given the sub-root*
/// — so the whole surface inherited the recorder's word. A compromised recorder could
/// record a sub-root it built itself and produce a valid-looking inclusion proof for
/// any balance, any spent nullifier, any note: the proof established one thing and the
/// storage said another, and consumers read the storage. An RWA vault gating on
/// "A holds >= N" was gating on the recorder.
///
/// Both unbound fields are GONE rather than documented:
///
///  * **height** is now proof-bound and read from the settlement contract.
///    `DreggSettlement` records the cumulative proven height per proven root
///    (`provenHeightOf`), which is `numTurns` accumulated over settlements that
///    passed the pairing check. There is nothing left to attest, so the height
///    argument was removed rather than checked.
///  * **the sub-roots** CANNOT be bound today, and the whole surface that read them
///    is deleted. See the named residual below for exactly what the proof would have
///    to expose. This follows `DreggSettlement`'s own precedent for the
///    operator-attested `outboundMessageRoot`: delete the recording path, refuse, and
///    state the circuit obligation.
///
/// With nothing left to attest, the RECORDER ROLE ITSELF IS GONE: `recordEpoch` is
/// permissionless, because every value it writes is determined by `settlement`. The
/// strongest available answer to "a compromised recorder forges X" is that there is
/// no recorder.
///
/// ## NAMED RESIDUAL — what the proof must expose (a LEAN-AUTHORED circuit change)
///
/// dregg's state commitment binds the sub-roots as Poseidon2/BabyBear FIELD elements
/// (`metatheory Dregg2.Circuit.StateCommit`: `RestHashIffFrame` lists `nullifierRoot`,
/// `revokedRoot`, `commitmentsRoot`, `heaps` among the hashed components). The
/// settlement statement is 25 lanes — `genesis_root[0..8) || final_root[8..16) ||
/// num_turns[16] || chain_digest[17..25)` — and carries NO sub-root.
///
/// Exposing the Poseidon2 sub-roots as extra lanes would NOT be enough. The sub-roots
/// this contract served were KECCAK mirrors: a different tree over the same set under
/// a different hash. An EVM contract cannot relate a Poseidon2 field root to a keccak
/// Merkle root, and no amount of on-chain Poseidon2 changes that. Binding these
/// requires the CIRCUIT to build the keccak mirror and prove it agrees with the
/// committed set — keccak-in-circuit over the four sets — and then to expose either
/// the four keccak roots or a single keccak commitment over them as additional apex
/// claim lanes. Concretely:
///
///   1. the apex claim absorbs a per-span sub-root commitment
///      `C = keccak(balanceRoot ++ nullifierRoot ++ commitmentsRoot ++ heapRoot)`,
///      proven equal to the keccak mirror of the sets the Poseidon2 state root commits;
///   2. `expose_claim` emits `C` as 8 further BabyBear lanes;
///   3. the shrink + gnark SettlementCircuit bind those lanes as public inputs
///      (25 → 33 lanes: a NEW Groth16 VK, hence a new `VK_DIGEST` on all three chains);
///   4. `settle` accepts the sub-root vector and checks `keccak(vector) == C` before
///      recording — at which point this contract can serve inclusion proofs again.
///
/// Steps 1–3 are AIR/constraint work and are authored in Lean under `metatheory/`,
/// with the Rust emit path following. They are NOT Solidity work and must not be
/// approximated here. Until they land there is no honest inclusion surface, so there
/// is none.
contract DreggStateOracle {
    // ─── Immutables ───────────────────────────────────────────────────────────

    /// The settlement client this oracle indexes. Read-only dependency, and the
    /// sole source of every fact this contract reports.
    IDreggSettlement public immutable settlement;

    // ─── State ─────────────────────────────────────────────────────────────────

    /// Ordered list of recorded state roots (enumeration / reorg windows). This is
    /// the ONE thing `DreggSettlement` cannot answer: it keys proven roots by hash
    /// with no ordering.
    bytes32[] public epochRoots;

    /// Whether `stateRoot` is already in `epochRoots` (append-once).
    mapping(bytes32 => bool) private _indexed;

    // ─── Events ────────────────────────────────────────────────────────────────

    /// `height` is `settlement.provenHeightOf(stateRoot)` — read, never supplied.
    event EpochRecorded(bytes32 indexed stateRoot, uint64 height, uint256 index);

    /// An inbound command/deposit commitment for dregg to ingest (the eth→dregg
    /// leg). dregg's relayer/light-client watches this log and mirrors the
    /// commitment into state. Value custody (if any) is held by a companion
    /// escrow; this event is the instruction channel.
    event InboundCommitment(bytes32 indexed commitment, address indexed from, bytes payload);

    // ─── Errors ────────────────────────────────────────────────────────────────

    error SettlementHasNoCode(address settlement);
    error StateRootNotProven(bytes32 stateRoot);
    error ZeroStateRoot();
    error EpochAlreadyRecorded(bytes32 stateRoot);
    error UnknownEpoch(bytes32 stateRoot);
    error EpochIndexOutOfRange(uint256 index, uint256 count);

    // ─── Constructor ────────────────────────────────────────────────────────────

    constructor(IDreggSettlement settlement_) {
        // Fail closed: a codeless settlement address would make isProvenRoot a
        // vacuous staticcall (the census fail-open pattern).
        if (address(settlement_).code.length == 0) {
            revert SettlementHasNoCode(address(settlement_));
        }
        settlement = settlement_;
    }

    // ─── The index ──────────────────────────────────────────────────────────────

    /// @notice Append a settled state root to the ordered epoch index. PERMISSIONLESS:
    ///         every value written is determined by `settlement`, so there is nothing
    ///         a caller could attest and nothing to gate.
    /// @param stateRoot the settled dregg state root (a `packLanes` key). MUST already
    ///        be proven by the settlement contract.
    /// @return index the position of `stateRoot` in `epochRoots`.
    function recordEpoch(bytes32 stateRoot) external returns (uint256 index) {
        if (stateRoot == bytes32(0)) revert ZeroStateRoot();
        // The load-bearing binding: only a genuinely settled state can be indexed.
        if (!settlement.isProvenRoot(stateRoot)) revert StateRootNotProven(stateRoot);
        if (_indexed[stateRoot]) revert EpochAlreadyRecorded(stateRoot);

        _indexed[stateRoot] = true;
        index = epochRoots.length;
        epochRoots.push(stateRoot);

        // Read, not supplied. `provenHeightOf` reverts for an unproven root, so this
        // cannot report a height for a state dregg never settled.
        emit EpochRecorded(stateRoot, settlement.provenHeightOf(stateRoot), index);
    }

    /// @notice Whether `stateRoot` has been appended to the index.
    /// @dev NOT a proxy for "is this root proven" — ask `settlement.isProvenRoot`.
    ///      A proven root that nobody has indexed yet answers false here.
    function isIndexed(bytes32 stateRoot) external view returns (bool) {
        return _indexed[stateRoot];
    }

    /// @notice Number of indexed epochs.
    function epochCount() external view returns (uint256) {
        return epochRoots.length;
    }

    /// @notice The `index`-th indexed state root, together with its PROOF-BOUND
    ///         height read from the settlement contract.
    function epochAt(uint256 index) external view returns (bytes32 stateRoot, uint64 height) {
        if (index >= epochRoots.length) {
            revert EpochIndexOutOfRange(index, epochRoots.length);
        }
        stateRoot = epochRoots[index];
        height = settlement.provenHeightOf(stateRoot);
    }

    // ─── Inbound commitments (eth → dregg, the instruction channel) ─────────────

    /// @notice Emit an inbound commitment for dregg to ingest. This is the
    ///         eth→dregg leg's instruction channel: dregg's relayer/light-client
    ///         watches `InboundCommitment` and mirrors the commitment into state.
    ///         Value custody (deposits) is handled by a companion escrow that
    ///         calls this; on its own it carries only instructions/commitments.
    function submitInbound(bytes32 commitment, bytes calldata payload) external {
        emit InboundCommitment(commitment, msg.sender, payload);
    }
}
