// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDreggSettlement} from "./IDreggSettlement.sol";
import {IGroth16Verifier25} from "./IGroth16Verifier25.sol";

/// Concrete dregg whole-history settlement contract at the modern 25-lane
/// proof shape. See `IDreggSettlement` for the pinned lane order, the
/// canonical BabyBear bound, and the state-machine semantics (the on-chain
/// twin of `bridge/src/ethereum.rs::{EthBridgeState, submit_eth_settlement}`).
contract DreggSettlement is IDreggSettlement {
    /// BabyBear prime p = 2^31 - 2^27 + 1. Every lane must be < p.
    uint256 public constant BABYBEAR_P = 2013265921;

    /// The pinned Groth16 verifier (VK baked in by gnark-solidity-verifier).
    IGroth16Verifier25 public immutable verifier;

    bytes32 private immutable _verifyingKeyHash;

    uint32[8] private _genesisLanes;
    uint32[8] private _provenLanes;
    uint64 private _provenHeight;

    /// Every dregg state root this contract has ever proven (packed key), incl.
    /// the genesis anchor. A cross-chain verifier (Hyperlane ISM, LayerZero DVN)
    /// checks a message against the root proven AT DISPATCH TIME, which by the
    /// time the message is processed is no longer `provenRoot()` — so historical
    /// proven roots must remain queryable. `bytes32(0)` is never recorded
    /// (the Nomad-law default), so `isProvenRoot(0)` is always false.
    mapping(bytes32 => bool) private _provenRoots;

    /// Every OUTBOUND MESSAGE ROOT recorded alongside a settlement: a keccak
    /// Merkle root over the cross-chain messages/events finalized in that span —
    /// an EVM-friendly (keccak) commitment DISTINCT from the dregg STATE root
    /// (`packLanes`, a keccak of 8 Poseidon/BabyBear lanes, under which no EVM
    /// contract can cheaply prove message inclusion). Interchain adapters
    /// (Hyperlane ISM, LayerZero DVN) verify a message's inclusion under one of
    /// these, gated by `isProvenMessageRoot`.
    ///
    /// NAMED RESIDUAL (honest scope, not laundered): the `settle` proof does NOT
    /// yet BIND `outboundMessageRoot` to the actual outbound messages — it is
    /// OPERATOR-ATTESTED at settle time (recorded only when a valid settlement
    /// proof lands, but the 25-lane proof does not constrain its contents).
    /// Making the message→root leg proof-carrying is a dregg-circuit obligation
    /// (expose the message root as a 26th proof public input, or fold it into
    /// `chainDigest` as a keccak-reconstructible commitment). `bytes32(0)` is
    /// never recorded.
    mapping(bytes32 => bool) private _provenMessageRoots;

    constructor(
        IGroth16Verifier25 verifier_,
        bytes32 verifyingKeyHash_,
        uint32[8] memory genesisRoot_
    ) {
        // Fail closed: a codeless verifier address must never be pinned.
        // (A staticcall to a codeless address "succeeds"; the census flagged
        // this exact fail-open pattern in the legacy contracts.)
        if (address(verifier_).code.length == 0) {
            revert VerifierHasNoCode(address(verifier_));
        }
        if (verifyingKeyHash_ == bytes32(0)) {
            revert ZeroVerifyingKeyHash();
        }
        verifier = verifier_;
        _verifyingKeyHash = verifyingKeyHash_;

        // The genesis anchor is pinned AT DEPLOYMENT, authenticated by the
        // deployer — mirroring `EthBridgeState::new(genesis_root)`
        // (bridge/src/ethereum.rs). It is NOT established by whoever calls
        // settle() first: since genesis_root is a public input to the wrapped
        // circuit (not baked into the VK), a first-caller-establishes model
        // would let anyone holding a valid proof over ANY dregg instance under
        // the same circuit VK front-run deployment and anchor a foreign chain.
        for (uint256 i = 0; i < 8; i++) {
            _requireCanonical(i, genesisRoot_[i]);
        }
        _genesisLanes = genesisRoot_;
        _provenLanes = genesisRoot_;
        _provenRoots[packLanes(genesisRoot_)] = true;
    }

    // ------------------------------------------------------------------
    // Views
    // ------------------------------------------------------------------

    /// True iff `root` (a `packLanes` key) has ever been proven by this contract
    /// (any historical proven root, plus the genesis anchor). `isProvenRoot(0)`
    /// is always false — the Nomad-law default is never accepted. Cross-chain
    /// verifiers gate message acceptance on this.
    function isProvenRoot(bytes32 root) external view returns (bool) {
        return _provenRoots[root];
    }

    /// True iff `messageRoot` was recorded by a settlement (any historical span).
    /// `isProvenMessageRoot(0)` is always false (the Nomad-law default). Adapters
    /// gate message-inclusion on this. See `_provenMessageRoots` for the
    /// operator-attested-vs-proof-bound residual.
    function isProvenMessageRoot(bytes32 messageRoot) external view returns (bool) {
        return _provenMessageRoots[messageRoot];
    }

    function provenRoot() external view returns (bytes32) {
        return packLanes(_provenLanes);
    }

    function provenRootLanes() external view returns (uint32[8] memory) {
        return _provenLanes;
    }

    function genesisAnchor() external view returns (bytes32) {
        return packLanes(_genesisLanes);
    }

    function genesisAnchorLanes() external view returns (uint32[8] memory) {
        return _genesisLanes;
    }

    /// Always true: the genesis anchor is pinned at construction. Retained for
    /// interface compatibility with the (former) first-settle-establishes model.
    function genesisEstablished() external pure returns (bool) {
        return true;
    }

    function provenHeight() external view returns (uint64) {
        return _provenHeight;
    }

    function verifyingKeyHash() external view returns (bytes32) {
        return _verifyingKeyHash;
    }

    /// keccak256 over the tight 32-byte big-endian packing of the 8 lanes:
    /// lane i occupies bytes [4i, 4i+4). Off-chain mirror for indexing.
    function packLanes(uint32[8] memory lanes) public pure returns (bytes32) {
        return keccak256(
            abi.encodePacked(
                lanes[0], lanes[1], lanes[2], lanes[3],
                lanes[4], lanes[5], lanes[6], lanes[7]
            )
        );
    }

    // ------------------------------------------------------------------
    // Settlement
    // ------------------------------------------------------------------

    function settle(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint32[8] calldata genesisRoot,
        uint32[8] calldata finalRoot,
        uint32 numTurns,
        uint32[8] calldata chainDigest,
        bytes32 outboundMessageRoot
    ) external {
        // `outboundMessageRoot` is NOT one of the 25 proof public inputs: it is
        // recorded (operator-attested, see `_provenMessageRoots`) so adapters can
        // verify message inclusion. Proof-binding it is the named residual.

        // 1. Every lane canonical BabyBear, and assemble the 25-lane vector
        //    in the pinned order: genesis[0..8) ++ final[8..16) ++
        //    numTurns[16] ++ chainDigest[17..25).
        uint256[25] memory inputs;
        for (uint256 i = 0; i < 8; i++) {
            _requireCanonical(i, genesisRoot[i]);
            inputs[i] = genesisRoot[i];
        }
        for (uint256 i = 0; i < 8; i++) {
            _requireCanonical(8 + i, finalRoot[i]);
            inputs[8 + i] = finalRoot[i];
        }
        _requireCanonical(16, numTurns);
        inputs[16] = numTurns;
        for (uint256 i = 0; i < 8; i++) {
            _requireCanonical(17 + i, chainDigest[i]);
            inputs[17 + i] = chainDigest[i];
        }

        // 2. Monotone height (mirrors `advance.height <= state.proven_height`
        //    rejection in submit_eth_settlement: height must strictly grow).
        if (numTurns == 0) revert ZeroTurns();

        // 3. Continuity (mirrors `advance.old_root != state.proven_root` +
        //    `proof.public_inputs.genesis_root != advance.old_root`): the
        //    proof's genesis lanes must equal the current proven root. The
        //    genesis anchor was pinned at construction, so the very first
        //    settle chains from it exactly like every later one.
        bytes32 packedOld = packLanes(_provenLanes);
        for (uint256 i = 0; i < 8; i++) {
            if (genesisRoot[i] != _provenLanes[i]) {
                revert ContinuityBroken(packedOld, packLanes(genesisRoot));
            }
        }

        // 4. The pairing check. Typed interface call: a false return OR a
        //    revert OR a codeless verifier all reject (fail closed).
        if (!verifier.verifyProof(a, b, c, inputs)) revert ProofRejected();

        // 5. Effects.
        _provenLanes = finalRoot;
        _provenHeight += numTurns;
        _provenRoots[packLanes(finalRoot)] = true;
        if (outboundMessageRoot != bytes32(0)) {
            _provenMessageRoots[outboundMessageRoot] = true;
        }

        emit Settled(packedOld, packLanes(finalRoot), _provenHeight);
        emit SettledLanes(genesisRoot, finalRoot, numTurns, chainDigest);
    }

    function _requireCanonical(uint256 laneIndex, uint32 value) private pure {
        if (uint256(value) >= BABYBEAR_P) {
            revert NonCanonicalLane(laneIndex, value);
        }
    }
}
